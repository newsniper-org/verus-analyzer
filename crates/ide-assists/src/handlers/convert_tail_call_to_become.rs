use syntax::{
    SyntaxNode, T,
    ast::{self, AstNode},
};

use crate::{AssistContext, AssistId, Assists};

// Assist: convert_tail_call_to_become
//
// Turns a call in tail position into a guaranteed tail call (`become`, which needs
// `#![feature(explicit_tail_calls)]`). Rust does not guarantee that an ordinary call in tail
// position replaces the caller's frame; Verus's `#[verifier::fip(strict)]` (constant stack
// space) needs recursion to go through `become`.
//
// ```
// fn sum(n: u64, acc: u64) -> u64 {
//     if n == 0 { acc } else { sum$0(n - 1, acc + n) }
// }
// ```
// ->
// ```
// fn sum(n: u64, acc: u64) -> u64 {
//     if n == 0 { acc } else { become sum(n - 1, acc + n) }
// }
// ```
pub(crate) fn convert_tail_call_to_become(
    acc: &mut Assists,
    ctx: &AssistContext<'_, '_>,
) -> Option<()> {
    let call: SyntaxNode = match (
        ctx.find_node_at_offset::<ast::CallExpr>(),
        ctx.find_node_at_offset::<ast::MethodCallExpr>(),
    ) {
        (Some(c), Some(m)) => {
            // the innermost of the two
            if c.syntax().text_range().len() <= m.syntax().text_range().len() {
                c.syntax().clone()
            } else {
                m.syntax().clone()
            }
        }
        (Some(c), None) => c.syntax().clone(),
        (None, Some(m)) => m.syntax().clone(),
        (None, None) => return None,
    };
    let ret = tail_position(&call)?;
    let target = call.text_range();
    acc.add(
        AssistId::refactor_rewrite("convert_tail_call_to_become"),
        "Convert to a tail call (`become`)",
        target,
        |builder| match &ret {
            Some(ret) => {
                if let Some(kw) = ret.syntax().first_token().filter(|t| t.kind() == T![return]) {
                    builder.replace(kw.text_range(), "become");
                }
            }
            None => builder.insert(call.text_range().start(), "become "),
        },
    )
}

/// Is `expr` in tail position of the enclosing function's body? `Some(Some(ret))` if it is the
/// operand of `return`, `Some(None)` if it is the value of the body
fn tail_position(expr: &SyntaxNode) -> Option<Option<ast::ReturnExpr>> {
    let mut cur = expr.clone();
    loop {
        let parent = cur.parent()?;
        if let Some(ret) = ast::ReturnExpr::cast(parent.clone()) {
            return (ret.expr()?.syntax() == &cur).then_some(Some(ret));
        }
        if let Some(stmts) = ast::StmtList::cast(parent.clone()) {
            if stmts.tail_expr()?.syntax() != &cur {
                return None;
            }
            let block = ast::BlockExpr::cast(stmts.syntax().parent()?)?;
            if block.syntax().parent().and_then(ast::Fn::cast).is_some() {
                return Some(None);
            }
            cur = block.syntax().clone();
            continue;
        }
        if let Some(if_expr) = ast::IfExpr::cast(parent.clone()) {
            let is_then = if_expr.then_branch().is_some_and(|b| b.syntax() == &cur);
            let is_else = match if_expr.else_branch() {
                Some(ast::ElseBranch::Block(b)) => b.syntax() == &cur,
                Some(ast::ElseBranch::IfExpr(i)) => i.syntax() == &cur,
                None => false,
            };
            if !is_then && !is_else {
                return None;
            }
            cur = parent;
            continue;
        }
        if let Some(arm) = ast::MatchArm::cast(parent.clone()) {
            if arm.expr()?.syntax() != &cur {
                return None;
            }
            let m = arm.syntax().ancestors().find_map(ast::MatchExpr::cast)?;
            cur = m.syntax().clone();
            continue;
        }
        if ast::ParenExpr::cast(parent.clone()).is_some() {
            cur = parent;
            continue;
        }
        return None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::tests::{check_assist, check_assist_not_applicable};

    #[test]
    fn tail_call_in_else_branch() {
        check_assist(
            convert_tail_call_to_become,
            "fn sum(n: u64, acc: u64) -> u64 { if n == 0 { acc } else { sum$0(n - 1, acc + n) } }",
            "fn sum(n: u64, acc: u64) -> u64 { if n == 0 { acc } else { become sum(n - 1, acc + n) } }",
        )
    }

    #[test]
    fn tail_call_after_return() {
        check_assist(
            convert_tail_call_to_become,
            "fn f(n: u64) -> u64 { if n == 0 { return 0; } return f$0(n - 1); }",
            "fn f(n: u64) -> u64 { if n == 0 { return 0; } become f(n - 1); }",
        )
    }

    #[test]
    fn tail_call_in_match_arm() {
        check_assist(
            convert_tail_call_to_become,
            "fn f(n: u64) -> u64 { match n { 0 => 0, _ => f$0(n - 1) } }",
            "fn f(n: u64) -> u64 { match n { 0 => 0, _ => become f(n - 1) } }",
        )
    }

    #[test]
    fn method_call_in_tail_position() {
        check_assist(
            convert_tail_call_to_become,
            "struct S; impl S { fn f(&self, n: u64) -> u64 { if n == 0 { 0 } else { self.f$0(n - 1) } } }",
            "struct S; impl S { fn f(&self, n: u64) -> u64 { if n == 0 { 0 } else { become self.f(n - 1) } } }",
        )
    }

    #[test]
    fn verus_function_with_spec() {
        check_assist(
            convert_tail_call_to_become,
            r#"
verus! {
fn sum(n: u64, acc: u64) -> (r: u64)
    decreases n
{
    if n == 0 { acc } else { sum$0(n - 1, acc) }
}
}
"#,
            r#"
verus! {
fn sum(n: u64, acc: u64) -> (r: u64)
    decreases n
{
    if n == 0 { acc } else { become sum(n - 1, acc) }
}
}
"#,
        )
    }

    #[test]
    fn not_in_tail_position() {
        check_assist_not_applicable(
            convert_tail_call_to_become,
            "fn f(n: u64) -> u64 { if n == 0 { 0 } else { 1 + f$0(n - 1) } }",
        )
    }

    #[test]
    fn not_for_a_statement() {
        check_assist_not_applicable(
            convert_tail_call_to_become,
            "fn f(n: u64) -> u64 { f$0(n); 0 }",
        )
    }

    #[test]
    fn not_for_become() {
        check_assist_not_applicable(
            convert_tail_call_to_become,
            "fn f(n: u64) -> u64 { become f$0(n - 1) }",
        )
    }

    #[test]
    fn not_in_a_closure() {
        check_assist_not_applicable(
            convert_tail_call_to_become,
            "fn f(n: u64) -> u64 { let g = |x: u64| f$0(x); g(n) }",
        )
    }
}

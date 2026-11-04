mod prefix_entries;
mod top_entries;

use std::{
    fmt::Write,
    fs,
    path::{Path, PathBuf},
};

use expect_test::expect_file;

use crate::{Edition, LexedStr, TopEntryPoint};

#[rustfmt::skip]
#[path = "../test_data/generated/runner.rs"]
mod runner;

fn infer_edition(file_path: &Path) -> Edition {
    let file_content = std::fs::read_to_string(file_path).unwrap();
    if let Some(edition) = file_content.strip_prefix("//@ edition: ") {
        edition[..4].parse().expect("invalid edition directive")
    } else {
        Edition::CURRENT
    }
}

#[test]
fn lex_ok() {
    for case in TestCase::list("lexer/ok") {
        let _guard = stdx::panic_context::enter(format!("{:?}", case.rs));
        let actual = lex(&case.text, infer_edition(&case.rs));
        expect_file![case.rast].assert_eq(&actual)
    }
}

#[test]
fn lex_err() {
    for case in TestCase::list("lexer/err") {
        let _guard = stdx::panic_context::enter(format!("{:?}", case.rs));
        let actual = lex(&case.text, infer_edition(&case.rs));
        expect_file![case.rast].assert_eq(&actual)
    }
}

fn lex(text: &str, edition: Edition) -> String {
    let lexed = LexedStr::new(edition, text);

    let mut res = String::new();
    for i in 0..lexed.len() {
        let kind = lexed.kind(i);
        let text = lexed.text(i);
        let error = lexed.error(i);

        let error = error.map(|err| format!(" error: {err}")).unwrap_or_default();
        writeln!(res, "{kind:?} {text:?}{error}").unwrap();
    }
    res
}

#[test]
fn parse_ok() {
    for case in TestCase::list("parser/ok") {
        let _guard = stdx::panic_context::enter(format!("{:?}", case.rs));
        let (actual, errors) = parse(TopEntryPoint::SourceFile, &case.text, Edition::CURRENT);
        assert!(!errors, "errors in an OK file {}:\n{actual}", case.rs.display());
        expect_file![case.rast].assert_eq(&actual);
    }
}

#[test]
fn parse_err() {
    for case in TestCase::list("parser/err") {
        let _guard = stdx::panic_context::enter(format!("{:?}", case.rs));
        let (actual, errors) = parse(TopEntryPoint::SourceFile, &case.text, Edition::CURRENT);
        assert!(errors, "no errors in an ERR file {}:\n{actual}", case.rs.display());
        expect_file![case.rast].assert_eq(&actual)
    }
}

#[test]
fn verus_keywords_remain_valid_rust_identifiers() {
    let source = r#"
fn f(mut matches: Matches) {
    for (_, m) in matches.by_node.drain() {
        matches.matches.push(m);
    }
    matches.matches.sort_by(|a, b| {});
    let _ = matches!(matches.kind, Kind::Plain | Kind::Self_);
}

struct tracked;
type Proof = proof_fn(tracked) -> i32;
type ProofResult = proof_fn() -> tracked;

mod tracked {
    struct Value;
}
type QualifiedProof = proof_fn(tracked::Value) -> tracked::Value;

fn proof_closure_parameter() {
    let _ = proof_fn|tracked: i32| tracked;
    let _ = proof_fn|tracked| tracked;
    let _ = proof_fn|tracked @ _| tracked;
}
"#;
    let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
    assert!(!errors, "{actual}");
}

#[test]
fn verus_macro_alias_is_a_transparent_item_wrapper() {
    let source = "verus_! { spec fn f() {} }";
    let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
    assert!(!errors, "{actual}");
    assert!(actual.lines().any(|line| line.trim() == "FN"), "{actual}");
    assert!(!actual.contains("MACRO_CALL"), "{actual}");
}

#[test]
fn verus_allocates_clause_parses() {
    // (source, number of ALLOCATES_CLAUSE nodes it should contain)
    let cases = [
        // a function, after the other clauses
        (
            r#"
verus! {
    fn f(n: usize) -> (r: u8)
        requires n > 0,
        ensures r == 0,
        no_unwind
        allocates n + 1
    {
        0
    }
}
"#,
            1,
        ),
        // a comma may follow the expression, as after `ensures`
        ("verus! { fn f() allocates 2, { } }", 1),
        // a list is a syntax-level match: only the macro insists on exactly one expression
        ("verus! { fn f() allocates 1, 2 { } }", 1),
        // `assume_specification`, with a complex bound
        (
            r#"
verus! {
    pub assume_specification<T>[ g::<T> ](x: T) -> (r: T)
        ensures r == x,
        allocates if true { 1int } else { 0int }
    ;
}
"#,
            1,
        ),
        // closures, with and without `ensures`
        (
            r#"
verus! {
    fn h() {
        let a = |y: u8| -> (r: u8) allocates 1 { y };
        let b = |y: u8| -> (r: u8) ensures r == y allocates 0 { y };
    }
}
"#,
            2,
        ),
        // `allocates` is contextual: it stays usable as an ordinary identifier
        ("verus! { fn f(allocates: u8) -> u8 { allocates } }", 0),
        ("verus! { fn f() { let allocates = 3; let _ = allocates + 1; } }", 0),
    ];
    for (source, expected) in cases {
        let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
        assert!(!errors, "{source}\n{actual}");
        let found = actual.lines().filter(|l| l.trim().starts_with("ALLOCATES_CLAUSE")).count();
        assert_eq!(found, expected, "{source}\n{actual}");
    }
}

/// Syntax that Verus accepts (it is in Verus's own test-suite) and that the parser must read
/// without errors. Each entry names the feature.
///
/// Four entries already parsed before the parser was brought up to date with Verus; they guard
/// the old behavior that the fixes sit next to: `global layout` with `align`, `tracked self`,
/// a constant named `proof`, and a closure body block that is followed by a comma.
#[test]
fn verus_syntax_catch_up_parses() {
    let cases = [
        ("global layout with size only", "verus! { global layout usize is size == 8; }"),
        (
            "global layout with size and align",
            "verus! { global layout S is size == 8, align == 4; }",
        ),
        ("tracked mut parameter", "verus! { proof fn f(tracked mut x: X, tracked y: Y) {} }"),
        (
            "tracked self parameters",
            "verus! { impl S { proof fn a(tracked self) {} proof fn b(tracked mut self) {} proof fn c(tracked &self) {} } }",
        ),
        (
            "const proof fn and const exec fn",
            "verus! { const proof fn p() {} pub const exec fn q() {} }",
        ),
        (
            "a constant named like a function mode",
            "verus! { const proof: u8 = 0; const exec: u8 = 1; }",
        ),
        (
            "proof_fn with named arguments",
            "verus! { type T = proof_fn(i: int, tracked j: int) -> int; }",
        ),
        (
            "proof_fn generics followed by options",
            "verus! { type T = proof_fn<'a>[Once](tracked E<'a>) -> (); }",
        ),
        (
            "proof_fn as a generic argument",
            "verus! { fn t(Tracked(f): Tracked<proof_fn[OpensInvariants](i: int)>) {} }",
        ),
        (
            "proof_fn returning a tracked never type",
            "verus! { proof fn r(tracked f: proof_fn() -> tracked !) {} }",
        ),
        (
            "opens_invariants on a closure",
            "verus! { fn t() { let f = proof_fn|i: int| requires i == 10 ensures true opens_invariants [3int] { }; } }",
        ),
        (
            "opens_invariants on a closure, followed by allocates",
            "verus! { fn t() { let f = |i: int| -> (r: int) ensures true opens_invariants any allocates 0 { i }; } }",
        ),
        (
            "a trigger attribute that carries its expressions",
            "verus! { spec fn f() -> bool { forall|x: int| #[trigger a(x)] c(x) } }",
        ),
        (
            "trigger expressions without commas",
            "verus! { fn f() ensures #![trigger double(x as int) half(r as int)] r == 1, {} }",
        ),
        (
            "auto trigger inside a parenthesized quantifier",
            "verus! { spec fn f() -> bool { forall (|i: int, j: int| #![auto] i < j ==> g(i)) } }",
        ),
        (
            "a clause that is a block expression followed by a comma",
            "verus! { fn f(t: S) requires { &&& a &&& b }, ensures { c }, { } }",
        ),
        (
            "the last clause of an atomically block",
            "verus! { fn f() atomically (au) { (old: T) -> (new: T), ensures new == old, }, { } }",
        ),
        (
            "matches followed by a logical or",
            "verus! { proof fn f() { assert(!(E::A matches E::A || true ==> false)); } }",
        ),
        (
            "matches with an or-pattern, then a logical or",
            "verus! { spec fn f(x: E) -> bool { x matches E::A | E::B || true } }",
        ),
        (
            "a comma after opens_invariants",
            "verus! { proof fn f() ensures true, opens_invariants [a, b], no_unwind { } proof fn g() opens_invariants any, { } }",
        ),
        (
            "generic paths in broadcast group and broadcast use",
            "verus! { broadcast group g { a::b, Seq::<_>::lemma, } broadcast use {c, Seq::<int>::lemma}; }",
        ),
        (
            "a closure body block followed by a comma is not a clause",
            "verus! { fn t(v: Vec<u32>) { let _ = v.into_iter().position(|i| -> (ret: bool) ensures ret == (i < 10), {i < 10},); } }",
        ),
    ];
    for (name, source) in cases {
        let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::Edition2021);
        assert!(!errors, "{name}\n{source}\n{actual}");
    }
}

#[test]
fn verus_syntax_extensions_parse() {
    let cases = [
        r#"
verus! {
    pub(crate) open spec fn compute(tracked x: int) -> (result: int)
        requires x >= 0,
        recommends x < 100,
        ensures result >= x,
        returns result
        decreases 100 - x when x < 100 via compute
        opens_invariants any
        no_unwind when x == 0
    {
        result
    }

    proof fn prove(a: int) {
        assert(a === a);
        assert(a !== a + 1);
        assert(a =~= a);
        assert(a =~~= a);
        assert(true ==> true);
        assert(true <== true);
        assert(true <==> true);
        assume(exists|x: int| x == a);
        let witness = choose|x: int| x == a;
        let quantified = forall|x: int|
            #![trigger identity(x)]
            identity(x) == x;
        assert forall|x: int| x == x by {}
    }

    spec fn conjunctions(a: bool, b: bool) -> bool {
        &&& a ==> a
        &&& b
        ||| a
        ||| b
    }
}
"#,
        r#"
verus! {
    ghost struct GhostState {
        tracked token: Token,
        ghost value: int,
    }

    tracked enum TrackedState {
        Empty,
        Full(tracked Token),
    }

    fn loops(v: Seq<int>) {
        let ghost snapshot = v;
        let tracked token: Token = get_token();
        while ready()
            invariant snapshot.len() == v.len(),
            decreases remaining(),
        {}
        loop
            invariant true,
            ensures true,
            decreases remaining(),
        {}
        for x in iter: v
            invariant v has x,
            decreases remaining(),
        {}
    }
}
"#,
        r#"
verus! {
    global size_of usize == 8;
    global layout Pair is size == 16, align == 8;

    broadcast group arithmetic {
        lemma_add,
        lemma_mul,
    }
    broadcast use {lemma_add, lemma_mul};

    assume_specification[external::function](x: int) -> int
        requires x >= 0,
        ensures x >= 0,
    ;

    proof fn postfix(v: Value, s: Set<Value>) {
        let view = v@;
        assert(v is Variant);
        assert(v !is Other);
        assert(s has v);
        assert(s !has view);
        assert(v->field == view);
        assert(v matches Variant { .. });
    }
}
"#,
        r#"
verus! {
    pub tracked struct Resource<T> {
        tracked value: T,
    }

    impl<T> Resource<T> {
        pub closed spec fn view(self) -> T {
            self.value
        }

        pub proof fn borrow(tracked &self) -> (tracked value: &T)
            ensures *value == self.value,
        {
            &self.value
        }

        pub axiom fn borrow_mut(tracked &mut self) -> tracked &mut T;
    }

    pub uninterp spec fn arbitrary<T>() -> T;

    pub broadcast axiom fn extensional<T>(left: T, right: T)
        ensures left === right,
    ;

    spec(checked) fn checked(value: int) -> nat
        recommends value >= 0,
        default_ensures true,
    {
        value as nat
    }

    proof fn apply<T, F>(
        tracked function: proof_fn<F>(tracked T) -> tracked T,
        tracked value: T,
    ) -> (tracked result: T) {
        function(value)
    }

    proof fn make<T>(tracked value: T) {
        let tracked function = move proof_fn[Once]|tracked input: T| -> (tracked output: T)
            requires true,
            ensures true,
        {
            input
        };
        let tracked _ = function(value);
    }

    fn loop_contracts() {
        loop
            invariant true,
            invariant_except_break true,
            ensures true,
            decreases 0,
        {}
    }
}
"#,
    ];

    for source in cases {
        let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
        assert!(!errors, "{actual}");
    }
}

#[test]
fn verus_named_tuple_return_type_parses() {
    let source = r#"
pub fn new() -> ((val, is_fresh): (u32, bool))
    requires true,
    ensures is_fresh,
{
    (0, true)
}

proof fn split() -> (tracked (left, right): (u32, bool))
    ensures right,
{
    (0, true)
}

fn parenthesized_tuple() -> ((u32, bool)) {
    (0, true)
}
"#;
    let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
    assert!(!errors, "{actual}");
}

#[test]
fn empty_verus_clause_lists_parse() {
    let source = r#"
fn empty_requires()
    requires
{}

fn empty_recommends()
    recommends
{}

fn empty_ensures()
    ensures
{}

fn empty_default_ensures()
    default_ensures
{}

fn empty_decreases()
    decreases
{}

fn empty_loop_clauses() {
    loop
        invariant
        invariant_except_break
        ensures
        decreases
    {}
}
"#;
    let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
    assert!(!errors, "{actual}");
}

#[test]
fn verus_clause_inner_attributes_parse() {
    let source = r#"
spec fn predicate() -> bool;

proof fn all_triggers()
    requires
        #![auto]
        predicate(),
    ensures
        #![all_triggers]
        predicate(),
{}

proof fn inferred_self<T: Trait>(value: T)
    ensures
        #![all_triggers]
        <_ as Trait>::predicate(&value),
{}
"#;
    let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
    assert!(!errors, "{actual}");
}

#[test]
fn verus_logical_atomicity_syntax_parses() {
    let source = r#"
fn atomic_function(px: PX) -> (py: PY)
    atomically (atomic_update) {
        type PredType,
        (ax: AX) -> (ay: AY),
        requires atomic_pre(px, ax),
        ensures atomic_post(px, ax, ay),
        outer_mask any / [namespace(px)],
        inner_mask [namespace(py)],
    },
    requires private_pre(px),
    ensures private_post(px, ax, ay, py),
{
    consume(atomic_update)
}

fn empty_atomic_spec()
    atomically (atomic_update) {},
{
    consume(atomic_update)
}

fn caller() {
    let py = atomic_function(px) 'retry: atomically loop |update| -> (au: AtomicUpdate)
        invariant_except_break can_retry(),
        invariant valid(),
        ensures done(),
    {
        let ay = update(ax);
        if ready() {
            break 'retry;
        }
        continue 'retry;
    };

    receiver.atomic_method() atomically |update,| -> (au) {
        update(ax);
    };
}
"#;
    let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
    assert!(!errors, "{actual}");
}

#[test]
fn verus_repeated_operators_do_not_split_longer_rust_token_runs() {
    let source = r#"
fn references(value: usize) {
    let _ = &&&&&&&value;
    let _ = &&&value;
    let _ = &&&(value);
}

fn contextual_identifiers(assert: Value, assume: Value) {
    assert.clone();
    assume.clone();
}

fn verus_operators(a: bool, b: bool) {
    let _ = &&& a;
    let _ = a &&& b;
    let _ = ||| a;
    let _ = a ||| b;
}
"#;
    let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
    assert!(!errors, "{actual}");
}

#[test]
fn incomplete_verus_syntax_recovers_to_following_items() {
    let cases = [
        r#"
verus! {
    proof fn incomplete(tracked value:) {}
    fn after() {}
}
"#,
        r#"
verus! {
    proof fn incomplete(value: int)
        requires value >,
    {}
    fn after() {}
}
"#,
        r#"
verus! {
    proof fn incomplete() {
        let tracked function = proof_fn[Once]|tracked value:| -> tracked;
    }
    fn after() {}
}
"#,
    ];

    for source in cases {
        let (actual, errors) = parse(TopEntryPoint::SourceFile, source, Edition::CURRENT);
        assert!(errors, "expected errors in:\n{actual}");
        assert!(actual.contains("IDENT \"after\""), "failed to recover in:\n{actual}");
    }
}

fn parse(entry: TopEntryPoint, text: &str, edition: Edition) -> (String, bool) {
    let lexed = LexedStr::new(edition, text);
    let input = lexed.to_input(edition);
    let output = entry.parse(&input);

    let mut buf = String::new();
    let mut errors = Vec::new();
    let mut indent = String::new();
    let mut depth = 0;
    let mut len = 0;
    lexed.intersperse_trivia(&output, &mut |step| match step {
        crate::StrStep::Token { kind, text } => {
            assert!(depth > 0);
            len += text.len();
            writeln!(buf, "{indent}{kind:?} {text:?}").unwrap();
        }
        crate::StrStep::Enter { kind } => {
            assert!(depth > 0 || len == 0);
            depth += 1;
            writeln!(buf, "{indent}{kind:?}").unwrap();
            indent.push_str("  ");
        }
        crate::StrStep::Exit => {
            assert!(depth > 0);
            depth -= 1;
            indent.pop();
            indent.pop();
        }
        crate::StrStep::Error { msg, pos } => {
            assert!(depth > 0);
            errors.push(format!("error {pos}: {msg}\n"))
        }
    });
    assert_eq!(
        len,
        text.len(),
        "didn't parse all text.\nParsed:\n{}\n\nAll:\n{}\n",
        &text[..len],
        text
    );

    for (token, msg) in lexed.errors() {
        let pos = lexed.text_start(token);
        errors.push(format!("error {pos}: {msg}\n"));
    }

    let has_errors = !errors.is_empty();
    for e in errors {
        buf.push_str(&e);
    }
    (buf, has_errors)
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct TestCase {
    rs: PathBuf,
    rast: PathBuf,
    text: String,
}

impl TestCase {
    fn list(path: &'static str) -> Vec<TestCase> {
        let crate_root_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let test_data_dir = crate_root_dir.join("test_data");
        let dir = test_data_dir.join(path);

        let mut res = Vec::new();
        let read_dir = fs::read_dir(&dir)
            .unwrap_or_else(|err| panic!("can't `read_dir` {}: {err}", dir.display()));
        for file in read_dir {
            let file = file.unwrap();
            let path = file.path();
            if path.extension().unwrap_or_default() == "rs" {
                let rs = path;
                let rast = rs.with_extension("rast");
                let text = fs::read_to_string(&rs).unwrap();
                res.push(TestCase { rs, rast, text });
            }
        }
        res.sort();
        res
    }
}

#[track_caller]
fn run_and_expect_no_errors(path: &str) {
    run_and_expect_no_errors_with_edition(path, Edition::CURRENT)
}

#[track_caller]
fn run_and_expect_errors(path: &str) {
    run_and_expect_errors_with_edition(path, Edition::CURRENT)
}

#[track_caller]
fn run_and_expect_no_errors_with_edition(path: &str, edition: Edition) {
    let path = PathBuf::from(path);
    let text = std::fs::read_to_string(&path).unwrap();
    let (actual, errors) = parse(TopEntryPoint::SourceFile, &text, edition);
    assert!(!errors, "errors in an OK file {}:\n{actual}", path.display());
    let mut p = PathBuf::from("..");
    p.push(path);
    p.set_extension("rast");
    expect_file![p].assert_eq(&actual)
}

#[track_caller]
fn run_and_expect_errors_with_edition(path: &str, edition: Edition) {
    let path = PathBuf::from(path);
    let text = std::fs::read_to_string(&path).unwrap();
    let (actual, errors) = parse(TopEntryPoint::SourceFile, &text, edition);
    assert!(errors, "no errors in an ERR file {}:\n{actual}", path.display());
    let mut p = PathBuf::from("..");
    p.push(path);
    p.set_extension("rast");
    expect_file![p].assert_eq(&actual)
}

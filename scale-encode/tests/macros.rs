#[test]
fn macro_compile_tests() {
    let t = trybuild::TestCases::new();
    t.pass("tests/macros/pass_*.rs");
    t.compile_fail("tests/macros/fail_*.rs");
}


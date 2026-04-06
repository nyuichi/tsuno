pub use tsuno_macros::{inv, verify};

#[doc(hidden)]
pub fn __tsuno_verify() {}

#[doc(hidden)]
pub fn __tsuno_assert(_value: bool) {}

#[doc(hidden)]
pub fn __tsuno_invariant(_value: bool) {}

#[macro_export]
macro_rules! invariant {
    ($cond:expr $(,)?) => {{
        $crate::inv!($cond);
    }};
}

#[macro_export]
macro_rules! assert {
    ($cond:expr $(,)?) => {{
        $crate::__tsuno_assert($cond);
    }};
}

pub use tsuno_macros::{invariant, verify};

#[doc(hidden)]
pub fn __tsuno_verify() {}

#[doc(hidden)]
pub fn __tsuno_assert(_value: bool) {}

#[doc(hidden)]
pub fn __tsuno_invariant(_value: bool) {}

#[macro_export]
macro_rules! assert {
    ($cond:expr $(,)?) => {{
        $crate::__tsuno_assert($cond);
    }};
}

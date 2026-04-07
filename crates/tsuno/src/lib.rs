pub use tsuno_macros::verify;

#[doc(hidden)]
pub fn __tsuno_verify() {}

#[doc(hidden)]
pub fn __tsuno_assert(_value: bool) {}

#[macro_export]
macro_rules! assert {
    ($cond:expr $(,)?) => {{
        $crate::__tsuno_assert($cond);
    }};
}

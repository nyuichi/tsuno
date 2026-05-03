struct Droppy {
    value: i32,
}

impl Drop for Droppy {
    fn drop(&mut self) {}
}

unsafe fn overwrite_drop_type(p: *mut Droppy) {
    *p = Droppy { value: 2i32 };
}

fn main() {}

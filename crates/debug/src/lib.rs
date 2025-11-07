///! Very simple crate for printing debug information at compile-time.
///! My needs were very simply so I didn't want to go all the way and
///! add a logging crate

pub const PRINT_DEBUG: bool = true;

#[macro_export]
macro_rules! debug {
    ($msg:literal $(,)?) => {
        {
            #[cfg(debug_assertions)]
            if $crate::PRINT_DEBUG {
                println!("\x1B[30m[{}:{}] \x1B[93m", file!(), line!());
                print!($msg);
                println!("\x1B[0m");
            }
        }
    };
    ($fmt:expr, $($arg:tt)*) => {
        {
            #[cfg(debug_assertions)]
            if $crate::PRINT_DEBUG {
                println!("\x1B[30m[{}:{}] \x1B[93m", file!(), line!());
                print!($fmt, $($arg)*);
                println!("\x1B[0m");
            }
        }
    };
}

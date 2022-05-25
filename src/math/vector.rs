use crate::number_traits::*;
use core::ops::*;

/// Remove the first `+` from tokens.
macro_rules! strip_plus {
    (+ $($rest:tt)*) => { $($rest)* };
}

/// Creates a new vector struct.
macro_rules! make_vector {
    (
        $name:ident, $size:expr, [$($member:ident),*],
        example_values: {
            a: [$($a:expr),*],
            b: [$($b:expr),*],
            i: [$($i:expr),*],
            num: $num:expr,
            sq_length: $sq_length:expr,
            length: $length:expr,
            add: [$($add:expr),*],
            sub: [$($sub:expr),*],
            mul: [$($mul:expr),*],
            mul_num: [$($mul_num:expr),*],
            div: [$($div:expr),*],
            div_num: [$($div_num:expr),*],
            neg: [$($neg:expr),*],
        }
    ) => {
        #[doc = concat!("A vector with ", stringify!($size), " components.")]
        #[derive(Copy, Clone, Debug, PartialEq, Eq)]
        pub struct $name<T: Number> { $(pub $member: T),* }

        impl<T: Number> $name<T> {
            /// Creates a vector with the given components.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let v = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("assert_eq!((", stringify!($(v.$member),*), "), (", stringify!($($a),*), "));")]
            /// ```
            #[inline]
            pub fn new($($member: T),*) -> Self {
                Self { $($member),* }
            }

            /// Returns the squared length of the vector.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let v = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("assert_eq!(v.length_sq(), ", stringify!($sq_length), ");")]
            /// ```
            #[inline]
            pub fn length_sq(self) -> T {
                strip_plus!($(+ self.$member * self.$member)*)
            }
        }

        impl<T: Integer> $name<T> {
            /// Returns the length of the vector with `f32`
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let v = ", stringify!($name), "::<i32>::new(", stringify!($($i),*), ");")]
            #[doc = concat!("assert_eq!(v.length_f32(), ", stringify!($length), "f32);")]
            /// ```
            #[inline]
            #[cfg(feature = "std")]
            pub fn length_f32(self) -> f32 {
                self.length_sq().to_f32().sqrt()
            }

            /// Returns the length of the vector with `f64`
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let v = ", stringify!($name), "::<i32>::new(", stringify!($($i),*), ");")]
            #[doc = concat!("assert_eq!(v.length_f64(), ", stringify!($length), "f64);")]
            /// ```
            #[inline]
            #[cfg(feature = "std")]
            pub fn length_f64(self) -> f64 {
                self.length_sq().to_f64().sqrt()
            }
        }

        impl<T: Float> $name<T> {
            /// Returns the length of the vector.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let v = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("assert_eq!(v.length(), ", stringify!($length), ");")]
            /// ```
            #[inline]
            #[cfg(feature = "std")]
            pub fn length(self) -> T {
                self.length_sq().sqrt()
            }

            /// Normalizes the vector.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let a = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            /// let v = a.normalize();
            /// assert_eq!(v.length(), 1.0);
            /// ```
            #[inline]
            #[cfg(feature = "std")]
            pub fn normalize(self) -> Self {
                self / self.length()
            }
        }

        impl<T: Number> Add for $name<T> {
            type Output = Self;

            /// Adds a vector to `self`.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let a = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("let b = ", stringify!($name), "::new(", stringify!($($b),*), ");")]
            /// let v = a + b;
            #[doc = concat!("assert_eq!((", stringify!($(v.$member),*), "), (", stringify!($($add),*), "));")]
            /// ```
            #[inline]
            fn add(self, other: Self) -> Self {
                Self { $($member: self.$member + other.$member),* }
            }
        }

        impl<T: Number> Sub for $name<T> {
            type Output = Self;

            /// Subtracts a vector from `self`.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let a = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("let b = ", stringify!($name), "::new(", stringify!($($b),*), ");")]
            /// let v = a - b;
            #[doc = concat!("assert_eq!((", stringify!($(v.$member),*), "), (", stringify!($($sub),*), "));")]
            /// ```
            #[inline]
            fn sub(self, other: Self) -> Self {
                Self { $($member: self.$member - other.$member),* }
            }
        }

        impl<T: Number> Mul for $name<T> {
            type Output = Self;

            /// Multiplies `self` by a vector.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let a = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("let b = ", stringify!($name), "::new(", stringify!($($b),*), ");")]
            /// let v = a * b;
            #[doc = concat!("assert_eq!((", stringify!($(v.$member),*), "), (", stringify!($($mul),*), "));")]
            /// ```
            #[inline]
            fn mul(self, other: Self) -> Self {
                Self { $($member: self.$member * other.$member),* }
            }
        }

        impl<T: Number> Mul<T> for $name<T> {
            type Output = Self;

            /// Multiplies `self` by a number.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let a = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("let v = a * ", stringify!($num), ";")]
            #[doc = concat!("assert_eq!((", stringify!($(v.$member),*), "), (", stringify!($($mul_num),*), "));")]
            /// ```
            #[inline]
            fn mul(self, other: T) -> Self {
                Self { $($member: self.$member * other),* }
            }
        }

        impl<T: Number> Div for $name<T> {
            type Output = Self;

            /// Divides `self` by a vector.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let a = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("let b = ", stringify!($name), "::new(", stringify!($($b),*), ");")]
            /// let v = a / b;
            #[doc = concat!("assert_eq!((", stringify!($(v.$member),*), "), (", stringify!($($div),*), "));")]
            /// ```
            #[inline]
            fn div(self, other: Self) -> Self {
                Self { $($member: self.$member / other.$member),* }
            }
        }

        impl<T: Number> Div<T> for $name<T> {
            type Output = Self;

            /// Divides `self` by a number.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let a = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            #[doc = concat!("let v = a / ", stringify!($num), ";")]
            #[doc = concat!("assert_eq!((", stringify!($(v.$member),*), "), (", stringify!($($div_num),*), "));")]
            /// ```
            #[inline]
            fn div(self, other: T) -> Self {
                Self { $($member: self.$member / other),* }
            }
        }

        impl<T: Signed> Neg for $name<T> {
            type Output = Self;

            /// Negates `self`.
            /// 
            /// # Examples
            /// 
            /// ```
            #[doc = concat!("use rutil::math::", stringify!($name), ";")]
            ///
            #[doc = concat!("let a = ", stringify!($name), "::new(", stringify!($($a),*), ");")]
            /// let v = -a;
            #[doc = concat!("assert_eq!((", stringify!($(v.$member),*), "), (", stringify!($($neg),*), "));")]
            /// ```
            #[inline]
            fn neg(self) -> Self {
                Self { $($member: -self.$member),* }
            }
        }
    };
}

make_vector! {
    Vec2, 2, [x, y],
    example_values: {
        a: [3.0, 4.0],
        b: [2.0, 10.0],
        i: [3, 4],
        num: 4.0,
        sq_length: 25.0,
        length: 5.0,
        add: [5.0, 14.0],
        sub: [1.0, -6.0],
        mul: [6.0, 40.0],
        mul_num: [12.0, 16.0],
        div: [1.5, 0.4],
        div_num: [0.75, 1.0],
        neg: [-3.0, -4.0],
    }
}

make_vector! {
    Vec3, 3, [x, y, z],
    example_values: {
        a: [3.0, 4.0, 0.0],
        b: [2.0, 10.0, 4.0],
        i: [3, 4, 0],
        num: 4.0,
        sq_length: 25.0,
        length: 5.0,
        add: [5.0, 14.0, 4.0],
        sub: [1.0, -6.0, -4.0],
        mul: [6.0, 40.0, 0.0],
        mul_num: [12.0, 16.0, 0.0],
        div: [1.5, 0.4, 0.0],
        div_num: [0.75, 1.0, 0.0],
        neg: [-3.0, -4.0, -0.0],
    }
}

make_vector! {
    Vec4, 4, [x, y, z, w],
    example_values: {
        a: [3.0, 4.0, 0.0, 12.0],
        b: [2.0, 10.0, 4.0, 6.0],
        i: [3, 4, 0, 12],
        num: 4.0,
        sq_length: 169.0,
        length: 13.0,
        add: [5.0, 14.0, 4.0, 18.0],
        sub: [1.0, -6.0, -4.0, 6.0],
        mul: [6.0, 40.0, 0.0, 72.0],
        mul_num: [12.0, 16.0, 0.0, 48.0],
        div: [1.5, 0.4, 0.0, 2.0],
        div_num: [0.75, 1.0, 0.0, 3.0],
        neg: [-3.0, -4.0, -0.0, -12.0],
    }
}

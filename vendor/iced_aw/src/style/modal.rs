//! Use a badge for color highlighting important information.
//!
//! *This API requires the following crate features to be activated: badge*

#[cfg(not(target_arch = "wasm32"))]
use iced_native::Background;

/// The appearance of a [`Modal`](crate::native::Modal).
#[derive(Clone, Copy, Debug)]
pub struct Style {
    /// The backgronud of the [`Modal`](crate::native::Modal).
    ///
    /// This is used to color the backdrop of the modal.
    pub background: Background,
}

/// The appearance of a [`Modal`](crate::native::Modal).
pub trait StyleSheet {
    /// The normal appearance of a [`Modal`](crate::native::Modal).
    fn active(&self) -> Style;
}

/// The default appearance of a [`Modal`](crate::native::Modal).
#[derive(Clone, Copy, Debug)]
pub struct Default;

impl StyleSheet for Default {
    fn active(&self) -> Style {
        Style {
            background: Background::Color([0.87, 0.87, 0.87, 0.30].into()),
        }
    }
}

#[allow(clippy::use_self)]
impl std::default::Default for Box<dyn StyleSheet> {
    fn default() -> Self {
        Box::new(Default)
    }
}

#[allow(clippy::use_self)]
impl<T> From<T> for Box<dyn StyleSheet>
where
    T: 'static + StyleSheet,
{
    fn from(style: T) -> Self {
        Box::new(style)
    }
}

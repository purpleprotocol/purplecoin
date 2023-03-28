//! Write some text for your users to read.
use crate::alignment;
use crate::layout;
use crate::renderer;
use crate::text;
use crate::{Color, Element, Layout, Length, Point, Rectangle, Size, Widget};
use zeroize::Zeroizing;

/// A paragraph of text.
///
/// # Example
///
/// ```
/// # type SafeText = iced_native::widget::SafeText<iced_native::renderer::Null>;
/// #
/// SafeText::new("I <3 iced!")
///     .color([0.0, 0.0, 1.0])
///     .size(40);
/// ```
///
/// ![SafeText drawn by `iced_wgpu`](https://github.com/iced-rs/iced/blob/7760618fb112074bc40b148944521f312152012a/docs/images/text.png?raw=true)
#[derive(Debug)]
pub struct SafeText<Renderer: text::Renderer> {
    content: Zeroizing<String>,
    size: Option<u16>,
    color: Option<Color>,
    font: Renderer::Font,
    width: Length,
    height: Length,
    horizontal_alignment: alignment::Horizontal,
    vertical_alignment: alignment::Vertical,
}

impl<Renderer: text::Renderer> SafeText<Renderer> {
    /// Create a new fragment of [`SafeText`] with the given contents.
    pub fn new<T: Into<String>>(label: T) -> Self {
        SafeText {
            content: Zeroizing::new(label.into()),
            size: None,
            color: None,
            font: Default::default(),
            width: Length::Shrink,
            height: Length::Shrink,
            horizontal_alignment: alignment::Horizontal::Left,
            vertical_alignment: alignment::Vertical::Top,
        }
    }

    /// Sets the size of the [`SafeText`].
    pub fn size(mut self, size: u16) -> Self {
        self.size = Some(size);
        self
    }

    /// Sets the [`Color`] of the [`SafeText`].
    pub fn color<C: Into<Color>>(mut self, color: C) -> Self {
        self.color = Some(color.into());
        self
    }

    /// Sets the [`Font`] of the [`SafeText`].
    ///
    /// [`Font`]: crate::text::Renderer::Font
    pub fn font(mut self, font: impl Into<Renderer::Font>) -> Self {
        self.font = font.into();
        self
    }

    /// Sets the width of the [`SafeText`] boundaries.
    pub fn width(mut self, width: Length) -> Self {
        self.width = width;
        self
    }

    /// Sets the height of the [`SafeText`] boundaries.
    pub fn height(mut self, height: Length) -> Self {
        self.height = height;
        self
    }

    /// Sets the [`alignment::Horizontal`] of the [`SafeText`].
    pub fn horizontal_alignment(
        mut self,
        alignment: alignment::Horizontal,
    ) -> Self {
        self.horizontal_alignment = alignment;
        self
    }

    /// Sets the [`alignment::Vertical`] of the [`SafeText`].
    pub fn vertical_alignment(
        mut self,
        alignment: alignment::Vertical,
    ) -> Self {
        self.vertical_alignment = alignment;
        self
    }
}

impl<Message, Renderer> Widget<Message, Renderer> for SafeText<Renderer>
where
    Renderer: text::Renderer,
{
    fn width(&self) -> Length {
        self.width
    }

    fn height(&self) -> Length {
        self.height
    }

    fn layout(
        &self,
        renderer: &Renderer,
        limits: &layout::Limits,
    ) -> layout::Node {
        let limits = limits.width(self.width).height(self.height);

        let size = self.size.unwrap_or(renderer.default_size());

        let bounds = limits.max();

        let (width, height) = renderer.measure(
            self.content.as_ref(),
            size,
            self.font.clone(),
            bounds,
        );

        let size = limits.resolve(Size::new(width, height));

        layout::Node::new(size)
    }

    fn draw(
        &self,
        renderer: &mut Renderer,
        style: &renderer::Style,
        layout: Layout<'_>,
        _cursor_position: Point,
        _viewport: &Rectangle,
    ) {
        draw(
            renderer,
            style,
            layout,
            self.content.as_ref(),
            self.font.clone(),
            self.size,
            self.color,
            self.horizontal_alignment,
            self.vertical_alignment,
        );
    }
}

/// Draws text using the same logic as the [`SafeText`] widget.
///
/// Specifically:
///
/// * If no `size` is provided, the default text size of the `Renderer` will be
///   used.
/// * If no `color` is provided, the [`renderer::Style::text_color`] will be
///   used.
/// * The alignment attributes do not affect the position of the bounds of the
///   [`Layout`].
pub fn draw<Renderer>(
    renderer: &mut Renderer,
    style: &renderer::Style,
    layout: Layout<'_>,
    content: &str,
    font: Renderer::Font,
    size: Option<u16>,
    color: Option<Color>,
    horizontal_alignment: alignment::Horizontal,
    vertical_alignment: alignment::Vertical,
) where
    Renderer: text::Renderer,
{
    let bounds = layout.bounds();

    let x = match horizontal_alignment {
        alignment::Horizontal::Left => bounds.x,
        alignment::Horizontal::Center => bounds.center_x(),
        alignment::Horizontal::Right => bounds.x + bounds.width,
    };

    let y = match vertical_alignment {
        alignment::Vertical::Top => bounds.y,
        alignment::Vertical::Center => bounds.center_y(),
        alignment::Vertical::Bottom => bounds.y + bounds.height,
    };

    renderer.fill_text(crate::text::Text {
        content,
        size: f32::from(size.unwrap_or(renderer.default_size())),
        bounds: Rectangle { x, y, ..bounds },
        color: color.unwrap_or(style.text_color),
        font,
        horizontal_alignment,
        vertical_alignment,
    });
}

impl<'a, Message, Renderer> From<SafeText<Renderer>>
    for Element<'a, Message, Renderer>
where
    Renderer: text::Renderer + 'a,
{
    fn from(text: SafeText<Renderer>) -> Element<'a, Message, Renderer> {
        Element::new(text)
    }
}

impl<Renderer: text::Renderer> Clone for SafeText<Renderer> {
    fn clone(&self) -> Self {
        Self {
            content: self.content.clone(),
            size: self.size,
            color: self.color,
            font: self.font.clone(),
            width: self.width,
            height: self.height,
            horizontal_alignment: self.horizontal_alignment,
            vertical_alignment: self.vertical_alignment,
        }
    }
}

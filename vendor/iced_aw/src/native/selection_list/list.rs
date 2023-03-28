//! Build and show dropdown `ListMenus`.
use crate::selection_list::Style;

use iced_native::{
    alignment::{Horizontal, Vertical},
    event,
    layout::{Limits, Node},
    mouse, renderer, touch, Clipboard, Color, Element, Event, Layout, Length, Point, Rectangle,
    Shell, Size, Widget,
};
use std::marker::PhantomData;

/// The Private [`List`] Handles the Actual list rendering.
#[allow(missing_debug_implementations)]
pub struct List<'a, T, Message, Renderer>
where
    Renderer: iced_native::Renderer + iced_native::text::Renderer<Font = iced_native::Font>,
{
    /// Options pointer to hold all rendered strings
    pub options: &'a [T],
    /// Hovered Item Pointer
    pub hovered_option: &'a mut Option<usize>,
    /// Last chosen Item Clicked for Processing
    pub last_selected_item: &'a mut Option<T>,
    /// The index in the list of options of the last chosen Item Clicked for Processing
    pub last_selected_index: Option<usize>,
    /// Label Font
    pub font: Renderer::Font,
    /// Style for Font colors and Box hover colors.
    pub style: Style,
    /// Function Pointer On Select to call on Mouse button press.
    pub on_selected: Box<dyn Fn(T) -> Message>,
    /// Shadow Type holder for Renderer.
    pub phantomdata: PhantomData<Renderer>,
}

impl<'a, T, Message, Renderer> Widget<Message, Renderer> for List<'a, T, Message, Renderer>
where
    T: Clone + ToString,
    Renderer: iced_native::Renderer + iced_native::text::Renderer<Font = iced_native::Font>,
{
    fn width(&self) -> Length {
        Length::Fill
    }

    fn height(&self) -> Length {
        Length::Shrink
    }

    fn layout(&self, _renderer: &Renderer, limits: &Limits) -> Node {
        use std::f32;
        let limits = limits.height(Length::Fill).width(Length::Fill);

        #[allow(clippy::cast_precision_loss)]
        let intrinsic = Size::new(
            limits.fill().width,
            f32::from(self.style.text_size + (self.style.padding * 2)) * self.options.len() as f32,
        );

        Node::new(intrinsic)
    }

    fn on_event(
        &mut self,
        event: Event,
        layout: Layout<'_>,
        cursor_position: Point,
        _renderer: &Renderer,
        _clipboard: &mut dyn Clipboard,
        shell: &mut Shell<Message>,
    ) -> event::Status {
        let bounds = layout.bounds();
        let mut status = event::Status::Ignored;

        if bounds.contains(cursor_position) {
            match event {
                Event::Mouse(mouse::Event::CursorMoved { .. }) => {
                    *self.hovered_option = Some(
                        ((cursor_position.y - bounds.y)
                            / f32::from(self.style.text_size + (self.style.padding * 2)))
                            as usize,
                    );
                }
                Event::Mouse(mouse::Event::ButtonPressed(mouse::Button::Left))
                | Event::Touch(touch::Event::FingerPressed { .. }) => {
                    *self.hovered_option = Some(
                        ((cursor_position.y - bounds.y)
                            / f32::from(self.style.text_size + (self.style.padding * 2)))
                            as usize,
                    );

                    if let Some(index) = self.hovered_option {
                        if let Some(option) = self.options.get(*index) {
                            *self.last_selected_item = Some(option.clone());
                            self.last_selected_index = Some(*index);
                        }
                    }

                    status =
                        self.last_selected_item
                            .take()
                            .map_or(event::Status::Ignored, |last| {
                                shell.publish((self.on_selected)(last));
                                event::Status::Captured
                            });
                }
                _ => {}
            }
        }

        status
    }

    fn mouse_interaction(
        &self,
        layout: Layout<'_>,
        cursor_position: Point,
        _viewport: &Rectangle,
        _renderer: &Renderer,
    ) -> mouse::Interaction {
        let bounds = layout.bounds();
        let is_mouse_over = bounds.contains(cursor_position);

        if is_mouse_over {
            mouse::Interaction::Pointer
        } else {
            mouse::Interaction::default()
        }
    }

    fn draw(
        &self,
        renderer: &mut Renderer,
        _style: &iced_native::renderer::Style,
        layout: iced_native::Layout<'_>,
        _cursor_position: iced_graphics::Point,
        viewport: &iced_graphics::Rectangle,
    ) {
        use std::f32;
        let bounds = layout.bounds();
        let option_height = self.style.text_size + (self.style.padding * 2);
        let offset = viewport.y - bounds.y;
        let start = (offset / f32::from(option_height)) as usize;
        let end = ((offset + viewport.height) / f32::from(option_height)).ceil() as usize;

        let visible_options = &self.options[start..end.min(self.options.len())];

        for (i, option) in visible_options.iter().enumerate() {
            let i = start + i;
            let is_selected = self.last_selected_index == Some(i);
            let is_hovered = *self.hovered_option == Some(i);

            let bounds = Rectangle {
                x: bounds.x,
                y: bounds.y + f32::from(option_height * i as u16),
                width: bounds.width,
                height: f32::from(self.style.text_size + (self.style.padding * 2)),
            };

            if is_selected || is_hovered {
                renderer.fill_quad(
                    renderer::Quad {
                        bounds,
                        border_radius: 0.0,
                        border_width: 0.0,
                        border_color: Color::TRANSPARENT,
                    },
                    if is_selected {
                        self.style.selected_background
                    } else {
                        self.style.hovered_background
                    },
                );
            }

            let text_color = if is_selected {
                self.style.selected_text_color
            } else if is_hovered {
                self.style.hovered_text_color
            } else {
                self.style.text_color
            };

            renderer.fill_text(iced_native::text::Text {
                content: &option.to_string(),
                bounds: Rectangle {
                    x: bounds.x,
                    y: bounds.center_y(),
                    width: f32::INFINITY,
                    ..bounds
                },
                size: f32::from(self.style.text_size),
                color: text_color,
                font: self.font,
                horizontal_alignment: Horizontal::Left,
                vertical_alignment: Vertical::Center,
            });
        }
    }
}

impl<'a, T, Message, Renderer> From<List<'a, T, Message, Renderer>>
    for Element<'a, Message, Renderer>
where
    T: ToString + Clone,
    Message: 'a,
    Renderer: 'a + iced_native::Renderer + iced_native::text::Renderer<Font = iced_native::Font>,
{
    fn from(list: List<'a, T, Message, Renderer>) -> Element<'a, Message, Renderer> {
        Element::new(list)
    }
}

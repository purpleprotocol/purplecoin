//! Display a dropdown list of selectable values.
pub mod list;
use crate::selection_list::Style;

use iced_native::{
    event,
    layout::{Limits, Node},
    mouse, renderer,
    widget::{scrollable, Container, Scrollable},
    Clipboard, Element, Event, Layout, Length, Point, Rectangle, Shell, Size, Widget,
};

pub use list::List;
use std::marker::PhantomData;

/// A widget for selecting a single value from a dynamic scrollable list of options.
#[allow(missing_debug_implementations)]
pub struct SelectionList<'a, T, Message, Renderer>
where
    T: Clone + ToString,
    Renderer: iced_native::Renderer + iced_native::text::Renderer<Font = iced_native::Font>,
{
    /// Container for Rendering List.
    container: Container<'a, Message, Renderer>,
    /// List of Elements to Render.
    options: &'a [T],
    /// Label Font
    font: Renderer::Font,
    /// Style for Looks
    style: Style,
}

/// The local state of a [`SelectionList`].
#[derive(Debug, Clone)]
pub struct State<T> {
    /// Statehood of Scrollbar
    scrollable: scrollable::State,
    /// Statehood of hovered_option
    hovered_option: Option<usize>,
    /// Statehood of last_selection
    last_selection: Option<T>,
}

impl<T> Default for State<T> {
    fn default() -> Self {
        Self {
            scrollable: scrollable::State::default(),
            hovered_option: Option::default(),
            last_selection: Option::default(),
        }
    }
}

impl<'a, T, Message, Renderer> SelectionList<'a, T, Message, Renderer>
where
    Message: 'a,
    Renderer: 'a + iced_native::Renderer + iced_native::text::Renderer<Font = iced_native::Font>,
    T: Clone + ToString + Eq,
{
    /// Creates a new [`SelectionList`] with the given [`State`], a list of options,
    /// the current selected value, and the message to produce when an option is
    /// selected.
    pub fn new(
        state: &'a mut State<T>,
        options: &'a [T],
        selected: &Option<T>,
        on_selected: impl Fn(T) -> Message + 'static,
        style: Style,
    ) -> Self {
        let State {
            hovered_option,
            last_selection,
            ..
        } = state;

        *hovered_option = options
            .iter()
            .position(|option| Some(option) == selected.as_ref());

        let last_selected_index = options
            .iter()
            .position(|option| Some(option) == selected.as_ref());

        let container = Container::new(Scrollable::new(&mut state.scrollable).push(List {
            options,
            hovered_option,
            last_selected_item: last_selection,
            last_selected_index,
            font: iced_graphics::Font::default(),
            style,
            on_selected: Box::new(on_selected),
            phantomdata: PhantomData::default(),
        }))
        .padding(1);

        Self {
            options,
            font: iced_graphics::Font::default(),
            style,
            container,
        }
    }
}

impl<'a, T, Message, Renderer> Widget<Message, Renderer> for SelectionList<'a, T, Message, Renderer>
where
    T: 'a + Clone + ToString + Eq,
    Message: 'static,
    Renderer: iced_native::Renderer + iced_native::text::Renderer<Font = iced_native::Font> + 'a,
{
    fn width(&self) -> Length {
        self.style.width
    }

    fn height(&self) -> Length {
        Length::Shrink
    }

    fn layout(&self, renderer: &Renderer, limits: &Limits) -> Node {
        use std::f32;

        let limits = limits.width(self.style.width).height(self.style.height);

        let max_width = match self.style.width {
            Length::Shrink => {
                let labels = self.options.iter().map(ToString::to_string);

                labels
                    .map(|label| {
                        let (width, _) = renderer.measure(
                            &label,
                            self.style.text_size,
                            self.font,
                            Size::new(f32::INFINITY, f32::INFINITY),
                        );

                        width.round() as u32 + u32::from(self.style.padding * 2)
                    })
                    .max()
                    .unwrap_or(100)
            }
            _ => limits.max().width as u32,
        };

        let limits = limits.max_width(max_width + u32::from(self.style.padding * 2));

        let content = self.container.layout(renderer, &limits);
        let size = limits.resolve(content.size());
        Node::with_children(size, vec![content])
    }

    fn on_event(
        &mut self,
        event: Event,
        layout: Layout<'_>,
        cursor_position: Point,
        renderer: &Renderer,
        clipboard: &mut dyn Clipboard,
        shell: &mut Shell<Message>,
    ) -> event::Status {
        self.container.on_event(
            event,
            layout
                .children()
                .next()
                .expect("Scrollable Child Missing in Selection List"),
            cursor_position,
            renderer,
            clipboard,
            shell,
        )
    }

    fn mouse_interaction(
        &self,
        layout: Layout<'_>,
        cursor_position: Point,
        viewport: &Rectangle,
        renderer: &Renderer,
    ) -> mouse::Interaction {
        self.container
            .mouse_interaction(layout, cursor_position, viewport, renderer)
    }

    fn draw(
        &self,
        renderer: &mut Renderer,
        style: &iced_native::renderer::Style,
        layout: Layout<'_>,
        cursor_position: Point,
        _viewport: &Rectangle,
    ) {
        renderer.fill_quad(
            renderer::Quad {
                bounds: layout.bounds(),
                border_color: self.style.border_color,
                border_width: self.style.border_width,
                border_radius: 0.0,
            },
            self.style.background,
        );

        self.container.draw(
            renderer,
            style,
            layout
                .children()
                .next()
                .expect("Scrollable Child Missing in Selection List"),
            cursor_position,
            &layout.bounds(),
        );
    }
}

impl<'a, T, Message, Renderer> From<SelectionList<'a, T, Message, Renderer>>
    for Element<'a, Message, Renderer>
where
    T: Clone + ToString + Eq,
    Message: 'static,
    Renderer: 'a + iced_native::Renderer + iced_native::text::Renderer<Font = iced_native::Font>,
{
    fn from(selection_list: SelectionList<'a, T, Message, Renderer>) -> Self {
        Element::new(selection_list)
    }
}

//! A modal for showing elements as an overlay on top of another.
//!
//! *This API requires the following crate features to be activated: modal*
use iced_native::{
    event, mouse, Clipboard, Element, Event, Layout, Point, Rectangle, Shell, Widget,
};

use super::overlay::modal::ModalOverlay;

pub use crate::style::modal::{Style, StyleSheet};

/// A modal content as an overlay.
///
/// Can be used in combination with the [`Card`](crate::native::card::Card)
/// widget to form dialog elements.
///
/// # Example
/// ```
/// # use iced_aw::native::modal;
/// # use iced_native::{widget::Text, renderer::Null};
/// #
/// # pub type Modal<'a, S, Content, Message>
/// #  = iced_aw::native::Modal<'a, Message, S, Content, Null>;
/// #[derive(Debug, Clone)]
/// enum Message {
///     CloseModal,
/// }
///
/// let mut state = modal::State::new(());
///
/// let modal = Modal::new(
///     &mut state,
///     Text::new("Underlay"),
///     |_state| Text::new("Overlay").into()
/// )
/// .backdrop(Message::CloseModal);
/// ```
#[allow(missing_debug_implementations)]
pub struct Modal<'a, S, Content, Message, Renderer>
where
    S: 'a,
    Content: Fn(&mut S) -> Element<'_, Message, Renderer>,
    Message: Clone,
    Renderer: iced_native::Renderer,
{
    /// The state of the [`Modal`](Modal).
    state: &'a mut State<S>,
    /// The underlying element.
    underlay: Element<'a, Message, Renderer>,
    /// The content of teh [`ModalOverlay`](ModalOverlay).
    content: Content,
    /// The optional message that will be send when the user clicked on the backdrop.
    backdrop: Option<Message>,
    /// The optional message that will be send when the ESC key was pressed.
    esc: Option<Message>,
    /// The style of the [`ModalOverlay`](ModalOverlay).
    style_sheet: Box<dyn StyleSheet>,
}

impl<'a, S, Content, Message, Renderer> Modal<'a, S, Content, Message, Renderer>
where
    S: 'a,
    Content: Fn(&mut S) -> Element<'_, Message, Renderer>,
    Message: Clone,
    Renderer: iced_native::Renderer,
{
    /// Creates a new [`Modal`](Modal) wrapping the underlying element to
    /// show some content as an overlay.
    ///
    /// `state` is the content's state, assigned at the creation of the
    /// overlying content.
    ///
    /// It expects:
    ///     * a mutable reference to the content's [`State`](State) of the [`Modal`](Modal).
    ///     * the underlay [`Element`](iced_native::Element) on which this [`Modal`](Modal)
    ///         will be wrapped around.
    ///     * the content [`Element`](iced_native::Element) of the [`Modal`](Modal).
    pub fn new<U>(state: &'a mut State<S>, underlay: U, content: Content) -> Self
    where
        U: Into<Element<'a, Message, Renderer>>,
    {
        Modal {
            state,
            underlay: underlay.into(),
            content,
            backdrop: None,
            esc: None,
            style_sheet: std::boxed::Box::default(),
        }
    }

    /// Sets the message that will be produced when the backdrop of the
    /// [`Modal`](Modal) is clicked.
    #[must_use]
    pub fn backdrop(mut self, message: Message) -> Self {
        self.backdrop = Some(message);
        self
    }

    /// Sets the message that will be produced when the Escape Key is
    /// pressed when the modal is open.
    ///
    /// This can be used to close the modal on ESC.
    #[must_use]
    pub fn on_esc(mut self, message: Message) -> Self {
        self.esc = Some(message);
        self
    }

    /// Sets the style of the [`Modal`](Modal).
    #[must_use]
    pub fn style(mut self, style_sheet: impl Into<Box<dyn StyleSheet>>) -> Self {
        self.style_sheet = style_sheet.into();
        self
    }
}

/// The state of the modal.
#[derive(Debug, Default)]
pub struct State<S> {
    /// The visibility of the [`Modal`](Modal) overlay.
    show: bool,
    /// The state of the content of the [`Modal`](Modal) overlay.
    state: S,
}

impl<S> State<S> {
    /// Creates a new [`State`](State) containing the given state data.
    pub const fn new(s: S) -> Self {
        Self {
            show: false,
            state: s,
        }
    }

    /// Setting this to true shows the modal (the modal is open), false means
    /// the modal is hidden (closed).
    pub fn show(&mut self, b: bool) {
        self.show = b;
    }

    /// See if this modal will be shown or not.
    pub const fn is_shown(&self) -> bool {
        self.show
    }

    /// Get a mutable reference to the inner state data.
    pub fn inner_mut(&mut self) -> &mut S {
        &mut self.state
    }

    /// Get a reference to the inner state data.
    pub const fn inner(&self) -> &S {
        &self.state
    }
}

impl<'a, S, Content, Message, Renderer> Widget<Message, Renderer>
    for Modal<'a, S, Content, Message, Renderer>
where
    S: 'a,
    Content: 'a + Fn(&mut S) -> Element<'_, Message, Renderer>,
    Message: 'a + Clone,
    Renderer: 'a + iced_native::Renderer,
{
    fn width(&self) -> iced_native::Length {
        self.underlay.width()
    }

    fn height(&self) -> iced_native::Length {
        self.underlay.height()
    }

    fn layout(
        &self,
        renderer: &Renderer,
        limits: &iced_native::layout::Limits,
    ) -> iced_native::layout::Node {
        self.underlay.layout(renderer, limits)
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
        self.underlay
            .on_event(event, layout, cursor_position, renderer, clipboard, shell)
    }

    fn mouse_interaction(
        &self,
        layout: Layout<'_>,
        cursor_position: Point,
        viewport: &Rectangle,
        renderer: &Renderer,
    ) -> mouse::Interaction {
        self.underlay
            .mouse_interaction(layout, cursor_position, viewport, renderer)
    }

    fn draw(
        &self,
        renderer: &mut Renderer,
        style: &iced_native::renderer::Style,
        layout: iced_native::Layout<'_>,
        cursor_position: iced_graphics::Point,
        viewport: &iced_graphics::Rectangle,
    ) {
        self.underlay
            .draw(renderer, style, layout, cursor_position, viewport);
    }

    fn overlay(
        &mut self,
        layout: Layout<'_>,
        renderer: &Renderer,
    ) -> Option<iced_native::overlay::Element<'_, Message, Renderer>> {
        if !self.state.show {
            return self.underlay.overlay(layout, renderer);
        }

        let bounds = layout.bounds();
        let position = Point::new(bounds.x, bounds.y);

        Some(
            ModalOverlay::new(
                &mut self.state.state,
                &self.content,
                self.backdrop.clone(),
                self.esc.clone(),
                &self.style_sheet,
            )
            .overlay(position),
        )
    }
}

impl<'a, State, Content, Message, Renderer> From<Modal<'a, State, Content, Message, Renderer>>
    for Element<'a, Message, Renderer>
where
    State: 'a,
    Content: 'a + Fn(&mut State) -> Element<'_, Message, Renderer>,
    Message: 'a + Clone,
    Renderer: 'a + iced_native::Renderer,
{
    fn from(modal: Modal<'a, State, Content, Message, Renderer>) -> Self {
        Element::new(modal)
    }
}

use iced::{
    pure::{
        widget::{Button, Column, Container, Scrollable, Text},
        Element, Sandbox,
    },
    Length, Settings,
};

use iced_aw::pure::floating_element::{self, FloatingElement};
use iced_aw::{Icon, ICON_FONT};

fn main() -> iced::Result {
    FloatingElementExample::run(Settings::default())
}

#[derive(Debug, Clone)]
enum Message {
    ButtonPressed,
}

struct FloatingElementExample {
    lines: Vec<String>,
}

impl Sandbox for FloatingElementExample {
    type Message = Message;

    fn new() -> Self {
        FloatingElementExample { lines: Vec::new() }
    }

    fn title(&self) -> String {
        String::from("FloatingButton example")
    }

    fn update(&mut self, message: Message) {
        match message {
            Message::ButtonPressed => self.lines.push("This is a newly added line.".into()),
        }
    }

    fn view(&self) -> Element<Message> {
        let scrollable_content = self.lines.iter().enumerate().fold(
            Column::new()
                .width(Length::Fill)
                .height(Length::Fill)
                .padding(10),
            |scroll, (i, line)| scroll.push(Text::new(format!("{}. {}", i + 1, line))),
        );
        let scrollable_content = Scrollable::new(scrollable_content);

        let content = FloatingElement::new(
            Container::new(scrollable_content)
                .width(Length::Fill)
                .height(Length::Fill)
                .max_width(400)
                .max_height(600)
                .style(BorderedContainer),
            || {
                Button::new(
                    Text::new(Icon::Plus)
                        .width(Length::Shrink)
                        .height(Length::Shrink)
                        .font(ICON_FONT)
                        .size(39),
                )
                //.style(iced_aw::style::button::Primary),
                .on_press(Message::ButtonPressed)
                .padding(5)
                .style(RoundedButton)
                .into()
            },
        )
        .anchor(floating_element::Anchor::SouthEast)
        .offset(20.0)
        .hide(false);

        Container::new(content)
            .width(Length::Fill)
            .height(Length::Fill)
            .padding(10)
            .center_x()
            .center_y()
            .into()
    }
}

struct RoundedButton;

impl iced::button::StyleSheet for RoundedButton {
    fn active(&self) -> iced::button::Style {
        iced::button::Style {
            border_radius: 25.0,
            ..iced_aw::style::button::Primary.active()
        }
    }
}

struct BorderedContainer;

impl iced::container::StyleSheet for BorderedContainer {
    fn style(&self) -> iced::container::Style {
        iced::container::Style {
            border_width: 1.0,
            border_color: iced::Color::BLACK,
            border_radius: 10.0,
            ..Default::default()
        }
    }
}

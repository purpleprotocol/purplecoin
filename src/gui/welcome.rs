// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::gui::{Icon, Message, Screen};
use iced::image::Handle;
use iced::widget::Image;
use iced::{
    alignment::Horizontal, button, Alignment, Button, Column, Container, Element, Length, Text,
};
use std::io;

#[derive(Debug, Clone)]
pub enum WelcomeMessage {
    NextPressed,
}

pub struct WelcomeScreen {
    button_state: button::State,
}

impl WelcomeScreen {
    pub fn new() -> Self {
        Self {
            button_state: button::State::new(),
        }
    }
}

impl Screen for WelcomeScreen {
    type Message = Message;

    fn title(&self) -> String {
        String::new()
    }

    fn content(&mut self) -> Element<'_, Self::Message> {
        let image = Image::new(Handle::from_pixels(
            crate::global::LOGO_PIXELS.1,
            crate::global::LOGO_PIXELS.2,
            crate::global::LOGO_PIXELS.0.clone(),
        ))
        .width(Length::Units(420))
        .height(Length::Units(420));

        let content: Element<'_, WelcomeMessage> = Container::new(
            Column::new()
                .align_items(Alignment::Center)
                .max_width(600)
                .padding(20)
                .spacing(16)
                .push(
                    Text::new("Welcome to Purplecoin!")
                        .size(48)
                        .horizontal_alignment(Horizontal::Center),
                )
                //.push(Container::new(image))
                .push(Text::new(
                    "Let's start by creating or importing your wallet",
                ))
                .push(
                    Button::new(&mut self.button_state, Text::new("Continue"))
                        .on_press(WelcomeMessage::NextPressed),
                ),
        )
        .into();

        content.map(Message::Welcome)
    }
}

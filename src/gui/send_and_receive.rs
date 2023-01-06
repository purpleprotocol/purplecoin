// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use iced::{slider, Alignment, Column, Container, Element, Length, Slider, Text};
use iced_aw::TabLabel;

use crate::gui::{Icon, Message, Tab};

#[derive(Debug, Clone)]
pub enum SendAndReceiveMessage {
    ImageWidthChanged(u16),
}

pub struct SendAndReceiveTab {
    ferris_width: u16,
    slider: slider::State,
}

impl SendAndReceiveTab {
    pub fn new() -> Self {
        SendAndReceiveTab {
            ferris_width: 100,
            slider: slider::State::default(),
        }
    }

    pub fn update(&mut self, message: SendAndReceiveMessage) {
        match message {
            SendAndReceiveMessage::ImageWidthChanged(value) => self.ferris_width = value,
        }
    }
}

impl Tab for SendAndReceiveTab {
    type Message = Message;

    fn title(&self) -> String {
        String::from("Send & Receive")
    }

    fn tab_label(&self) -> TabLabel {
        TabLabel::IconText(Icon::Heart.into(), self.title())
    }

    fn content(&mut self) -> Element<'_, Self::Message> {
        let content: Element<'_, SendAndReceiveMessage> = Container::new(
            Column::new()
                .align_items(Alignment::Center)
                .max_width(600)
                .padding(20)
                .spacing(16)
                .push(Text::new(if self.ferris_width == 500 {
                    "Hugs!!!"
                } else {
                    "Pull me closer!"
                }))
                .push(Slider::new(
                    &mut self.slider,
                    100..=500,
                    self.ferris_width,
                    SendAndReceiveMessage::ImageWidthChanged,
                )),
        )
        .into();

        content.map(Message::SendAndReceive)
    }
}

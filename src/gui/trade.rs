// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::gui::{Icon, Message, Tab};
use iced::{button, Alignment, Button, Column, Container, Element, Row, Text};
use iced_aw::TabLabel;
#[derive(Debug, Clone)]
pub enum TradeMessage {
    Increase,
    Decrease,
}

pub struct TradeTab {
    value: i32,
    increase_button: button::State,
    decrease_button: button::State,
}

impl TradeTab {
    pub fn new() -> Self {
        TradeTab {
            value: 0,
            increase_button: button::State::default(),
            decrease_button: button::State::default(),
        }
    }

    pub fn update(&mut self, message: TradeMessage) {
        match message {
            TradeMessage::Increase => self.value += 1,
            TradeMessage::Decrease => self.value -= 1,
        }
    }
}

impl Tab for TradeTab {
    type Message = Message;

    fn title(&self) -> String {
        String::from("Exchange")
    }

    fn tab_label(&self) -> TabLabel {
        //TabLabel::Text(self.title())
        TabLabel::IconText(Icon::Calc.into(), self.title())
    }

    fn content(&mut self) -> Element<'_, Self::Message> {
        let content: Element<'_, TradeMessage> = Container::new(
            Column::new()
                .align_items(Alignment::Center)
                .max_width(600)
                .padding(20)
                .spacing(16)
                .push(Text::new(format!("Count: {}", self.value)).size(32))
                .push(
                    Row::new()
                        .spacing(10)
                        .push(
                            Button::new(&mut self.decrease_button, Text::new("Decrease"))
                                .on_press(TradeMessage::Decrease),
                        )
                        .push(
                            Button::new(&mut self.increase_button, Text::new("Increase"))
                                .on_press(TradeMessage::Increase),
                        ),
                ),
        )
        .into();

        content.map(Message::Trade)
    }
}

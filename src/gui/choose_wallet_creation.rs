// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::gui::{Message, Screen};
use iced::{
    alignment::Horizontal, button, Alignment, Button, Column, Container, Element, Row, Text,
};
use std::io;

#[derive(Debug, Clone)]
pub enum ChooseWalletCreationMessage {
    CreatePressed,
    ImportPressed,
}

pub struct ChooseWalletCreationScreen {
    create_button_state: button::State,
    import_button_state: button::State,
}

impl ChooseWalletCreationScreen {
    pub fn new() -> Self {
        Self {
            create_button_state: button::State::new(),
            import_button_state: button::State::new(),
        }
    }
}

impl Screen for ChooseWalletCreationScreen {
    type Message = Message;

    fn title(&self) -> String {
        String::from("")
    }

    fn content(&mut self) -> Element<'_, Self::Message> {
        let content: Element<'_, ChooseWalletCreationMessage> = Container::new(
            Column::new()
                .align_items(Alignment::Center)
                .max_width(600)
                .padding(20)
                .spacing(16)
                .push(
                    Text::new("Create or import wallet")
                        .size(48)
                        .horizontal_alignment(Horizontal::Center),
                )
                .push(
                    Row::new()
                        .push(
                            Column::new().push(
                                Column::new()
                                    .align_items(Alignment::Center)
                                    .padding(10)
                                    .push(
                                        Button::new(
                                            &mut self.create_button_state,
                                            Text::new("Create wallet"),
                                        )
                                        .on_press(ChooseWalletCreationMessage::CreatePressed),
                                    ),
                            ),
                        )
                        .push(
                            Column::new().push(
                                Column::new()
                                    .align_items(Alignment::Center)
                                    .padding(10)
                                    .push(
                                        Button::new(
                                            &mut self.import_button_state,
                                            Text::new("Import wallet"),
                                        )
                                        .on_press(ChooseWalletCreationMessage::ImportPressed),
                                    ),
                            ),
                        ),
                ),
        )
        .into();

        content.map(Message::ChooseWalletCreation)
    }
}

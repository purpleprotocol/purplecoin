// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::gui::{Icon, Message, Screen};
use bip39::{Mnemonic, MnemonicType, Language};
use iced::image::Handle;
use iced::widget::Image;
use iced::{
    alignment::Horizontal, button, Alignment, Button, Column, Container, Element, Length, Text,
};
use std::io;

#[derive(Debug, Clone)]
pub enum CreateWalletMessage {
    RenderMnemonic,
    ConfirmMnemonic,
    Done,
}

enum CreateWalletState<'a> {
    Null,
    RenderMnemonic(Mnemonic, Box<String>),
    ConfirmMnemonic(Mnemonic),
}

pub struct CreateWalletScreen<'a> {
    to_render_button_state: button::State,
    to_confirm_button_state: button::State,
    to_overview_button_state: button::State,
    state: CreateWalletState<'a>,
}

impl CreateWalletScreen {
    pub fn new() -> Self {
        Self {
            to_render_button_state: button::State::new(),
            to_confirm_button_state: button::State::new(),
            to_overview_button_state: button::State::new(),
            state: CreateWalletState::Null,
        }
    }

    pub fn update(&mut self, message: CreateWalletMessage) {
        match message {
            CreateWalletMessage::RenderMnemonic => {
                self.state = CreateWalletState::RenderMnemonic(Mnemonic::new(MnemonicType::Words24, Language::English))
            }
            CreateWalletMessage::ConfirmMnemonic => {
                if let CreateWalletState::RenderMnemonic(mnemonic, content_ptr) = self.state {
                    self.state = CreateWalletState::ConfirmMnemonic(mnemonic.clone());
                    content_ptr.zeroize();
                } else {
                    unreachable!()
                }
            }
            _ => unimplemented!()
        }
    }
}

impl Screen for CreateWalletScreen {
    type Message = Message;

    fn title(&self) -> String {
        String::from("")
    }

    fn content(&mut self) -> Element<'_, Self::Message> {
        match self.state {
            CreateWalletState::Null => {
                let content: Element<'_, CreateWalletMessage> = Container::new(
                    Column::new()
                        .align_items(Alignment::Center)
                        .max_width(600)
                        .padding(20)
                        .spacing(16)
                        .push(
                            Text::new("Generate recovery phrase")
                                .size(48)
                                .horizontal_alignment(Horizontal::Center),
                        )
                        .push(Text::new(
                            "We will start by generating a 24 word recovery phrase for your wallet. Write it down on a piece of paper and keep it safe. You risk losing your assets if you lose the recovery phrase.",
                        ))
                        .push(Text::new(
                            "You risk losing your assets if you lose the recovery phrase.",
                        ).size(24))
                        .push(
                            Button::new(&mut self.to_render_button_state, Text::new("Continue"))
                                .on_press(CreateWalletMessage::RenderMnemonic),
                        ),
                )
                .into();
        
                content.map(Message::CreateWallet)
            }

            CreateWalletState::RenderMnemonic(ref mnemonic, content_ptr) => {
                let secure_text = Text::new(
                    mnemonic.phrase(),
                ).size(24);

                // We need to keep a separate pointer to the secure text content so we can zeroize it later
                content_ptr = Some(&secure_text.content);

                let content: Element<'_, CreateWalletMessage> = Container::new(
                    Column::new()
                        .align_items(Alignment::Center)
                        .max_width(600)
                        .padding(20)
                        .spacing(16)
                        .push(
                            Text::new("Write down recovery phrase")
                                .size(48)
                                .horizontal_alignment(Horizontal::Center),
                        )
                        .push(secure_text)
                        .push(Text::new(
                            "Write these on a piece of paper and keep it safe.",
                        ))
                        .push(
                            Button::new(&mut self.to_render_button_state, Text::new("Continue"))
                                .on_press(CreateWalletMessage::RenderMnemonic),
                        ),
                )
                .into();
        
                content.map(Message::CreateWallet)
            }
        
            _ => unimplemented!()
        }
    }
}

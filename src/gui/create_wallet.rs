// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::gui::{Icon, Message, Screen};
use bip39::{Language, Mnemonic, MnemonicType};
use iced::image::Handle;
use iced::widget::Image;
use iced::{
    alignment::Horizontal, button, Alignment, Button, Column, Container, Element, Length, Checkbox,
    SafeText as Text,
};
use std::io;
use zeroize::{Zeroize, Zeroizing};

#[derive(Debug, Clone)]
pub enum CreateWalletMessage {
    RenderMnemonic,
    ConfirmMnemonic,
    ChooseWalletNameAndPassword,
    CheckboxToggled(bool),
    Done,
}

enum CreateWalletState {
    Null,
    RenderMnemonic(Mnemonic),
    ChooseWalletNameAndPassword(Mnemonic),
    ConfirmMnemonic(Mnemonic, String, Zeroizing<String>),
}

pub struct CreateWalletScreen {
    to_render_button_state: button::State,
    to_confirm_button_state: button::State,
    to_overview_button_state: button::State,
    is_checked: bool,

    // Encryption key for password state
    // 
    // We encrypt the wallet password before it is being passed to the text input
    // and we decrypt it when the local state is being updated. We then zeroize
    // the encryption key and the local state once we are done. In this way we do
    // not leave any readable traces in memory.
    pass_encr_key: [u8; 32],

    state: CreateWalletState,
}

impl CreateWalletScreen {
    pub fn new() -> Self {
        Self {
            to_render_button_state: button::State::new(),
            to_confirm_button_state: button::State::new(),
            to_overview_button_state: button::State::new(),
            is_checked: false,
            state: CreateWalletState::Null,
        }
    }

    pub fn reset(&mut self) -> {
        self.is_checked = false;
        self.state = CreateWalletState::Null;
    }

    pub fn update(&mut self, message: CreateWalletMessage) {
        match message {
            CreateWalletMessage::RenderMnemonic => {
                self.state = CreateWalletState::RenderMnemonic(Mnemonic::new(
                    MnemonicType::Words24,
                    Language::English,
                ))
            }
            CreateWalletMessage::ConfirmMnemonic => {
                let mut mnemonic = None;
                if let CreateWalletState::RenderMnemonic(mn) = &mut self.state {
                    mnemonic = Some(mn.clone());
                } else {
                    unreachable!()
                }

                self.state = CreateWalletState::ConfirmMnemonic(mnemonic.unwrap());
            }
            CreateWalletMessage::ChooseWalletNameAndPassword => {
                let mut mnemonic = None;
                if let CreateWalletState::RenderMnemonic(mn) = &mut self.state {
                    mnemonic = Some(mn.clone());
                } else {
                    unreachable!()
                }

                self.state = CreateWalletState::ChooseWalletNameAndPassword(mnemonic.unwrap());
            }
            CreateWalletMessage::CheckboxToggled(state) => {
                self.is_checked = state;
            }
            _ => unimplemented!(),
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
                            "We will start by generating a 24 word recovery phrase for your wallet. Write it down on a piece of paper and keep it safe.",
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

            CreateWalletState::RenderMnemonic(ref mnemonic) => {
                if self.is_checked {
                    let secure_text = Text::new(mnemonic.phrase()).size(28);

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
                                "Write these on a piece of paper and keep it safe. Make sure to double check that it is correct before continuing.",
                            ))
                            .push(
                                Checkbox::new(self.is_checked, "I have written down my recovery phrase and double checked that it is correct.", CreateWalletMessage::CheckboxToggled))
                            .push(
                                Button::new(&mut self.to_render_button_state, Text::new("Continue"))
                                    .on_press(CreateWalletMessage::ChooseWalletNameAndPassword),
                            ),
                    )
                    .into();

                    content.map(Message::CreateWallet)
                } else {
                    let secure_text = Text::new(mnemonic.phrase()).size(28);

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
                                "Write these on a piece of paper and keep it safe. Make sure to double check that it is correct before continuing.",
                            ))
                            .push(
                                Checkbox::new(self.is_checked, "I have written down my recovery phrase and double checked that it is correct.", CreateWalletMessage::CheckboxToggled))
                    )
                    .into();

                    content.map(Message::CreateWallet)
                }
            }

            CreateWalletState::ChooseWalletNameAndPassword(mnemonic) => {
                let secure_text = Text::new(mnemonic.phrase()).size(28);

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
                            "Write these on a piece of paper and keep it safe. Make sure to double check that it is correct before continuing.",
                        ))
                        .push(
                            Checkbox::new(self.is_checked, "I have written down my recovery phrase and double checked that it is correct.", CreateWalletMessage::CheckboxToggled))
                )
                .into();

                content.map(Message::CreateWallet)
            }

            _ => unimplemented!()
        }
    }
}

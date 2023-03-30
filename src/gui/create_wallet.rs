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
    alignment::Horizontal, button, text_input, Alignment, Button, Checkbox, Column, Container,
    Element, Length, SafeText as Text, TextInput,
};
use std::io;
use zeroize::{Zeroize, Zeroizing};

#[derive(Debug, Clone)]
pub enum CreateWalletMessage {
    RenderMnemonic,
    ConfirmMnemonic,
    ChooseWalletNameAndPassword,
    CheckboxToggled(bool),
    WalletNameChanged(String),
    PasswordChanged(String),
    PasswordConfirmChanged(String),
    Done,
}

pub(crate) enum CreateWalletState {
    Null,
    RenderMnemonic(Mnemonic),
    ChooseWalletNameAndPassword(Mnemonic, String, Zeroizing<String>),
    ConfirmMnemonic(Mnemonic, String, Zeroizing<String>),
}

pub struct CreateWalletScreen {
    to_render_button_state: button::State,
    to_confirm_button_state: button::State,
    to_overview_button_state: button::State,
    create_wallet_button_state: button::State,
    wallet_name_state: text_input::State,
    wallet_password_state: text_input::State,
    wallet_password_confirm_state: text_input::State,
    wallet_name: String,
    password: String,
    password_confirm: String,
    is_checked: bool,
    pub(crate) state: CreateWalletState,
}

impl CreateWalletScreen {
    pub fn new() -> Self {
        Self {
            to_render_button_state: button::State::new(),
            to_confirm_button_state: button::State::new(),
            to_overview_button_state: button::State::new(),
            create_wallet_button_state: button::State::new(),
            wallet_name_state: text_input::State::new(),
            wallet_password_state: text_input::State::new(),
            wallet_password_confirm_state: text_input::State::new(),
            wallet_name: String::new(),
            password: String::new(),
            password_confirm: String::new(),
            is_checked: false,
            state: CreateWalletState::Null,
        }
    }

    pub fn reset(&mut self) {
        self.is_checked = false;
        self.wallet_name_state = text_input::State::new();
        self.wallet_password_state = text_input::State::new();
        self.wallet_password_confirm_state = text_input::State::new();
        self.password.zeroize();
        self.password_confirm.zeroize();
        self.password = String::new();
        self.password_confirm = String::new();
        self.wallet_name = String::new();
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
            CreateWalletMessage::ChooseWalletNameAndPassword => {
                let mnemonic = if let CreateWalletState::RenderMnemonic(mn) = &self.state {
                    mn.clone()
                } else {
                    unreachable!()
                };

                self.state = CreateWalletState::ChooseWalletNameAndPassword(
                    mnemonic,
                    String::new(),
                    Zeroizing::new(String::new()),
                );
            }
            CreateWalletMessage::ConfirmMnemonic => {
                let mnemonic =
                    if let CreateWalletState::ChooseWalletNameAndPassword(mn, _, _) = &self.state {
                        mn.clone()
                    } else {
                        unreachable!()
                    };

                self.state = CreateWalletState::ConfirmMnemonic(
                    mnemonic,
                    self.wallet_name.clone(),
                    Zeroizing::new(self.password.clone()),
                );
            }
            CreateWalletMessage::WalletNameChanged(name) => {
                self.wallet_name = name;
            }
            CreateWalletMessage::PasswordChanged(mut password) => {
                self.password = password.clone();
                password.zeroize();
            }
            CreateWalletMessage::PasswordConfirmChanged(mut password_confirm) => {
                self.password_confirm = password_confirm.clone();
                password_confirm.zeroize();
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
        match &self.state {
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

            CreateWalletState::ChooseWalletNameAndPassword(mnemonic, wallet_name, password) => {
                let content: Element<'_, CreateWalletMessage> =
                    if self.password.is_empty() && self.password_confirm.is_empty() {
                        Container::new(
                            Column::new()
                                .align_items(Alignment::Center)
                                .max_width(600)
                                .padding(20)
                                .spacing(16)
                                .push(
                                    Text::new("Choose wallet name and password")
                                        .size(48)
                                        .horizontal_alignment(Horizontal::Center),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_name_state,
                                        "Wallet name",
                                        &self.wallet_name,
                                        CreateWalletMessage::WalletNameChanged,
                                    )
                                    .padding(10),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_password_state,
                                        "Password",
                                        &self.password,
                                        CreateWalletMessage::PasswordChanged,
                                    )
                                    .password()
                                    .padding(10),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_password_confirm_state,
                                        "Password confirmation",
                                        &self.password_confirm,
                                        CreateWalletMessage::PasswordConfirmChanged,
                                    )
                                    .password()
                                    .padding(10),
                                ),
                        )
                        .into()
                    } else if self.password.len() < 6 && self.password != self.password_confirm {
                        Container::new(
                            Column::new()
                                .align_items(Alignment::Center)
                                .max_width(600)
                                .padding(20)
                                .spacing(16)
                                .push(
                                    Text::new("Choose wallet name and password")
                                        .size(48)
                                        .horizontal_alignment(Horizontal::Center),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_name_state,
                                        "Wallet name",
                                        &self.wallet_name,
                                        CreateWalletMessage::WalletNameChanged,
                                    )
                                    .padding(10),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_password_state,
                                        "Password",
                                        &self.password,
                                        CreateWalletMessage::PasswordChanged,
                                    )
                                    .password()
                                    .padding(10),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_password_confirm_state,
                                        "Password confirmation",
                                        &self.password_confirm,
                                        CreateWalletMessage::PasswordConfirmChanged,
                                    )
                                    .password()
                                    .padding(10),
                                )
                                .push(
                                    Text::new("The password must be greater than 6 characters")
                                        .size(18),
                                ),
                        )
                        .into()
                    } else if self.password != self.password_confirm {
                        Container::new(
                            Column::new()
                                .align_items(Alignment::Center)
                                .max_width(600)
                                .padding(20)
                                .spacing(16)
                                .push(
                                    Text::new("Choose wallet name and password")
                                        .size(48)
                                        .horizontal_alignment(Horizontal::Center),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_name_state,
                                        "Wallet name",
                                        &self.wallet_name,
                                        CreateWalletMessage::WalletNameChanged,
                                    )
                                    .padding(10),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_password_state,
                                        "Password",
                                        &self.password,
                                        CreateWalletMessage::PasswordChanged,
                                    )
                                    .password()
                                    .padding(10),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_password_confirm_state,
                                        "Password confirmation",
                                        &self.password_confirm,
                                        CreateWalletMessage::PasswordConfirmChanged,
                                    )
                                    .password()
                                    .padding(10),
                                )
                                .push(
                                    Text::new("The password must match the password confirmation")
                                        .size(18),
                                ),
                        )
                        .into()
                    } else {
                        Container::new(
                            Column::new()
                                .align_items(Alignment::Center)
                                .max_width(600)
                                .padding(20)
                                .spacing(16)
                                .push(
                                    Text::new("Choose wallet name and password")
                                        .size(48)
                                        .horizontal_alignment(Horizontal::Center),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_name_state,
                                        "Wallet name",
                                        &self.wallet_name,
                                        CreateWalletMessage::WalletNameChanged,
                                    )
                                    .padding(10),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_password_state,
                                        "Password",
                                        &self.password,
                                        CreateWalletMessage::PasswordChanged,
                                    )
                                    .password()
                                    .padding(10),
                                )
                                .push(
                                    TextInput::new(
                                        &mut self.wallet_password_confirm_state,
                                        "Password confirmation",
                                        &self.password_confirm,
                                        CreateWalletMessage::PasswordConfirmChanged,
                                    )
                                    .password()
                                    .padding(10),
                                )
                                .push(
                                    Button::new(
                                        &mut self.create_wallet_button_state,
                                        Text::new("Continue"),
                                    )
                                    .on_press(CreateWalletMessage::ConfirmMnemonic),
                                ),
                        )
                        .into()
                    };

                content.map(Message::CreateWallet)
            }

            _ => unimplemented!(),
        }
    }
}

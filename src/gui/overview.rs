// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use iced::{
    alignment::{Alignment, Horizontal, Vertical},
    button, text_input, Button, Column, Container, Element, Length, Row, Rule, Text, TextInput,
};
use iced_aw::TabLabel;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use std::str::FromStr;

use crate::gui::{Icon, Message, Tab};

#[derive(Debug, Clone)]
pub enum OverviewMessage {
    UsernameChanged(String),
    PasswordChanged(String),
    ClearPressed,
    OverviewPressed,
}

pub struct OverviewTab {
    username: String,
    username_state: text_input::State,
    password: String,
    password_state: text_input::State,
    clear_button: button::State,
    login_button: button::State,
}

impl OverviewTab {
    pub fn new() -> Self {
        OverviewTab {
            username: String::new(),
            username_state: text_input::State::default(),
            password: String::new(),
            password_state: text_input::State::default(),
            clear_button: button::State::default(),
            login_button: button::State::default(),
        }
    }

    pub fn update(&mut self, message: OverviewMessage) {
        match message {
            OverviewMessage::UsernameChanged(value) => self.username = value,
            OverviewMessage::PasswordChanged(value) => self.password = value,
            OverviewMessage::ClearPressed => {
                self.username = String::new();
                self.password = String::new();
            }
            OverviewMessage::OverviewPressed => {}
        }
    }
}

impl Tab for OverviewTab {
    type Message = Message;

    fn title(&self) -> String {
        String::from("")
    }

    fn tab_label(&self) -> TabLabel {
        TabLabel::IconText(Icon::User.into(), "Overview".to_owned())
    }

    fn content(&mut self) -> Element<'_, Self::Message> {
        let coin_str: String = format!("{}", crate::consensus::COIN);
        let coin = Decimal::from_str(&coin_str).unwrap();
        let available: Decimal = crate::global::get_balance("hot").into();
        let pending = dec!(0);
        let total = available + pending;
        let available = available.checked_div(coin).unwrap();
        let pending = pending.checked_div(coin).unwrap();
        let total = total.checked_div(coin).unwrap();

        let content: Element<'_, OverviewMessage> = Container::new(
            Row::new()
                .align_items(Alignment::Start)
                .push(
                    Column::new()
                        .align_items(Alignment::Start)
                        .padding(16)
                        //.spacing(16)
                        .push(
                            Row::new()
                                .align_items(Alignment::Fill)
                                .push(Text::new("Balances XPU").size(32)),
                        )
                        .push(
                            Row::new()
                                .align_items(Alignment::Fill)
                                .push(
                                    Text::new("Available:")
                                        .size(16)
                                        .horizontal_alignment(Horizontal::Left)
                                        .width(Length::FillPortion(1)),
                                )
                                .push(
                                    Text::new(format!("{available:.18}  XPU"))
                                        .size(16)
                                        .horizontal_alignment(Horizontal::Right)
                                        .width(Length::FillPortion(1)),
                                ),
                        )
                        .push(
                            Row::new()
                                .align_items(Alignment::Fill)
                                .push(
                                    Text::new("Pending:")
                                        .size(16)
                                        .horizontal_alignment(Horizontal::Left)
                                        .width(Length::FillPortion(1)),
                                )
                                .push(
                                    Text::new(format!("{pending:.18}  XPU"))
                                        .size(16)
                                        .horizontal_alignment(Horizontal::Right)
                                        .width(Length::FillPortion(1)),
                                ),
                        )
                        .push(Rule::horizontal(4))
                        .push(
                            Row::new()
                                .align_items(Alignment::Fill)
                                .push(
                                    Text::new("Total:")
                                        .size(16)
                                        .horizontal_alignment(Horizontal::Left)
                                        .width(Length::FillPortion(1)),
                                )
                                .push(
                                    Text::new(format!("{total:.18}  XPU"))
                                        .size(16)
                                        .horizontal_alignment(Horizontal::Right)
                                        .width(Length::FillPortion(1)),
                                ),
                        )
                        .width(Length::FillPortion(1))
                        .height(Length::Fill),
                )
                .push(
                    Column::new()
                        .align_items(Alignment::Start)
                        .padding(16)
                        .push(Text::new("Recent transactions").size(32))
                        .push(
                            Row::new().align_items(Alignment::Fill).push(
                                Row::new()
                                    .align_items(Alignment::Fill)
                                    .push(Text::new("No transactions available").size(20)),
                            ),
                        )
                        .width(Length::FillPortion(1))
                        .height(Length::Fill),
                )
                .width(Length::Fill)
                .height(Length::Fill),
        )
        .width(Length::Fill)
        .height(Length::Fill)
        .align_x(Horizontal::Center)
        .align_y(Vertical::Center)
        .into();

        content.map(Message::Overview)
    }
}

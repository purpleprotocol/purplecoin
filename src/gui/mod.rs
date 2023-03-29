// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use iced::executor;
use iced::{
    alignment::{Horizontal, Vertical},
    Application, Column, Command, Container, Element, Font, Length, Settings, Subscription, Text,
};
use iced_futures::backend::default::time;

use iced_aw::{TabLabel, Tabs};

mod overview;
use overview::{OverviewMessage, OverviewTab};

mod send_and_receive;
use send_and_receive::{SendAndReceiveMessage, SendAndReceiveTab};

mod trade;
use trade::{TradeMessage, TradeTab};

mod settings;
use settings::{SettingsMessage, SettingsTab, TabBarPosition};

mod welcome;
use welcome::{WelcomeMessage, WelcomeScreen};

mod choose_wallet_creation;
use choose_wallet_creation::{ChooseWalletCreationMessage, ChooseWalletCreationScreen};

mod create_wallet;
use create_wallet::{CreateWalletMessage, CreateWalletScreen, CreateWalletState};

mod import_wallet;
mod import_wallet_file;
mod import_wallet_mnemonic;
mod import_wallet_private_key;

use std::time::{Duration, Instant};

mod theme;

const HEADER_SIZE: u16 = 32;
const TAB_PADDING: u16 = 16;
const SCREEN_PADDING: u16 = 16;
const WINDOW_TITLE: &str = "Purplecoin Core";

const ICON_FONT: Font = iced::Font::External {
    name: "Icons",
    bytes: include_bytes!("./fonts/icons.ttf"),
};

enum Icon {
    User,
    Heart,
    Calc,
    CogAlt,
}

enum ActiveScreen {
    Welcome,
    Tabs,
    ImportWallet,
    ImportWalletMnemonic,
    ImportWalletFile,
    ImportWalletPrivateKey,
    CreateWallet,
    CreateWalletMnemonicBackup,
    CreateWalletMnemonicConfirm,
    ChooseWalletCreation,
}

impl From<Icon> for char {
    fn from(icon: Icon) -> Self {
        match icon {
            Icon::User => '\u{F015}',
            Icon::Heart => '\u{F19C}',
            Icon::Calc => '\u{F0EC}',
            Icon::CogAlt => '\u{F013}',
        }
    }
}

pub struct GUI {
    active_tab: usize,
    active_screen: ActiveScreen,
    overview_tab: OverviewTab,
    send_and_receive_tab: SendAndReceiveTab,
    trade_tab: TradeTab,
    settings_tab: SettingsTab,
    welcome_screen: WelcomeScreen,
    choose_wallet_creation_screen: ChooseWalletCreationScreen,
    create_wallet_screen: CreateWalletScreen,
}

#[derive(Clone, Debug)]
pub enum Message {
    // Tabs
    TabSelected(usize),
    Overview(OverviewMessage),
    SendAndReceive(SendAndReceiveMessage),
    Trade(TradeMessage),
    Settings(SettingsMessage),

    // Screens
    Welcome(WelcomeMessage),
    ChooseWalletCreation(ChooseWalletCreationMessage),
    CreateWallet(CreateWalletMessage),

    // Global
    Tick(Instant),
}

impl Application for GUI {
    type Executor = executor::Default;
    type Message = Message;
    type Flags = ();

    fn new(_: Self::Flags) -> (Self, Command<Self::Message>) {
        let active_screen = if crate::global::WALLETS.read().is_empty() {
            ActiveScreen::Welcome
        } else {
            ActiveScreen::Tabs
        };

        (
            GUI {
                active_tab: 0,
                active_screen,
                overview_tab: OverviewTab::new(),
                send_and_receive_tab: SendAndReceiveTab::new(),
                trade_tab: TradeTab::new(),
                settings_tab: SettingsTab::new(),
                welcome_screen: WelcomeScreen::new(),
                choose_wallet_creation_screen: ChooseWalletCreationScreen::new(),
                create_wallet_screen: CreateWalletScreen::new(),
            },
            Command::none(),
        )
    }

    fn title(&self) -> String {
        format!("{} v{}", WINDOW_TITLE, env!("CARGO_PKG_VERSION"))
    }

    fn update(&mut self, message: Self::Message) -> Command<Self::Message> {
        match message {
            Message::TabSelected(selected) => self.active_tab = selected,
            Message::Overview(message) => self.overview_tab.update(message),
            Message::SendAndReceive(message) => self.send_and_receive_tab.update(message),
            Message::Trade(message) => self.trade_tab.update(message),
            Message::Settings(message) => self.settings_tab.update(message),
            Message::Welcome(WelcomeMessage::NextPressed) => {
                self.active_screen = ActiveScreen::ChooseWalletCreation
            }
            Message::ChooseWalletCreation(ChooseWalletCreationMessage::CreatePressed) => {
                self.active_screen = ActiveScreen::CreateWallet
            }
            Message::ChooseWalletCreation(ChooseWalletCreationMessage::ImportPressed) => {
                self.active_screen = ActiveScreen::ImportWallet
            }
            Message::CreateWallet(CreateWalletMessage::ConfirmMnemonic) => {
                self.create_wallet_screen
                    .update(CreateWalletMessage::ConfirmMnemonic);

                // Create wallet and dump it to disk
                if let CreateWalletState::ConfirmMnemonic(mnemonic, name, password) =
                    &self.create_wallet_screen.state
                {
                    crate::wallet::gen_hdwallet_bip39(&name, password.as_ref(), mnemonic.clone())
                        .unwrap();
                } else {
                    unreachable!();
                };
                crate::wallet::load_wallets();
                self.overview_tab.reload_wallets();
                self.create_wallet_screen.reset();
                self.active_screen = ActiveScreen::Tabs;
            }
            Message::CreateWallet(message) => self.create_wallet_screen.update(message),
            Message::Tick(_) => {}
        }

        Command::none()
    }

    fn view(&mut self) -> Element<'_, Self::Message> {
        match self.active_screen {
            ActiveScreen::Tabs => {
                let position = self
                    .settings_tab
                    .settings()
                    .tab_bar_position
                    .unwrap_or_default();
                let theme = self
                    .settings_tab
                    .settings()
                    .tab_bar_theme
                    .unwrap_or_default();

                Tabs::new(self.active_tab, Message::TabSelected)
                    .push(self.overview_tab.tab_label(), self.overview_tab.view())
                    .push(
                        self.send_and_receive_tab.tab_label(),
                        self.send_and_receive_tab.view(),
                    )
                    .push(self.trade_tab.tab_label(), self.trade_tab.view())
                    .push(self.settings_tab.tab_label(), self.settings_tab.view())
                    .tab_bar_style(theme)
                    .icon_font(ICON_FONT)
                    .tab_bar_position(match position {
                        TabBarPosition::Top => iced_aw::TabBarPosition::Top,
                        TabBarPosition::Bottom => iced_aw::TabBarPosition::Bottom,
                    })
                    .into()
            }

            ActiveScreen::Welcome => self.welcome_screen.view(),
            ActiveScreen::ChooseWalletCreation => self.choose_wallet_creation_screen.view(),
            ActiveScreen::CreateWallet => self.create_wallet_screen.view(),

            _ => {
                unimplemented!()
            }
        }
    }

    fn subscription(&self) -> Subscription<Message> {
        time::every(Duration::from_millis(10)).map(Message::Tick)
    }
}

trait Tab {
    type Message;

    fn title(&self) -> String;

    fn tab_label(&self) -> TabLabel;

    fn view(&mut self) -> Element<'_, Self::Message> {
        let column = Column::new()
            .spacing(20)
            .push(Text::new(self.title()).size(HEADER_SIZE))
            .push(self.content());

        Container::new(column)
            .width(Length::Fill)
            .height(Length::Fill)
            .align_x(Horizontal::Center)
            .align_y(Vertical::Center)
            .padding(TAB_PADDING)
            .into()
    }

    fn content(&mut self) -> Element<'_, Self::Message>;
}

trait Screen {
    type Message;

    fn title(&self) -> String;

    fn view(&mut self) -> Element<'_, Self::Message> {
        let column = Column::new()
            .spacing(20)
            .push(Text::new(self.title()).size(HEADER_SIZE))
            .push(self.content());

        Container::new(column)
            .width(Length::Fill)
            .height(Length::Fill)
            .align_x(Horizontal::Center)
            .align_y(Vertical::Center)
            .padding(SCREEN_PADDING)
            .into()
    }

    fn content(&mut self) -> Element<'_, Self::Message>;
}

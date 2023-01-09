// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
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
use std::time::{Duration, Instant};

mod theme;

const HEADER_SIZE: u16 = 32;
const TAB_PADDING: u16 = 16;
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

impl From<Icon> for char {
    fn from(icon: Icon) -> Self {
        match icon {
            Icon::User => '\u{E800}',
            Icon::Heart => '\u{E801}',
            Icon::Calc => '\u{F1EC}',
            Icon::CogAlt => '\u{E802}',
        }
    }
}

pub struct GUI {
    active_tab: usize,
    overview_tab: OverviewTab,
    send_and_receive_tab: SendAndReceiveTab,
    trade_tab: TradeTab,
    settings_tab: SettingsTab,
}

#[derive(Clone, Debug)]
pub enum Message {
    TabSelected(usize),
    Overview(OverviewMessage),
    SendAndReceive(SendAndReceiveMessage),
    Trade(TradeMessage),
    Settings(SettingsMessage),
    Tick(Instant),
}

impl Application for GUI {
    type Executor = executor::Default;
    type Message = Message;
    type Flags = ();

    fn new(_: Self::Flags) -> (Self, Command<Self::Message>) {
        (
            GUI {
                active_tab: 0,
                overview_tab: OverviewTab::new(),
                send_and_receive_tab: SendAndReceiveTab::new(),
                trade_tab: TradeTab::new(),
                settings_tab: SettingsTab::new(),
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
            Message::Tick(_) => {}
        }

        Command::none()
    }

    fn view(&mut self) -> Element<'_, Self::Message> {
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

        let mut aaa = Tabs::new(self.active_tab, Message::TabSelected);
        println!("1");
        aaa = aaa.push(self.overview_tab.tab_label(), self.overview_tab.view());
        println!("1");
        aaa = aaa.push(
            self.send_and_receive_tab.tab_label(),
            self.send_and_receive_tab.view(),
        );
        println!("1");
        aaa = aaa.push(self.trade_tab.tab_label(), self.trade_tab.view());
        println!("1");
        aaa = aaa.push(self.settings_tab.tab_label(), self.settings_tab.view());
        println!("1");
        aaa = aaa.tab_bar_style(theme);
        println!("1");
        aaa = aaa.icon_font(ICON_FONT);
        println!("1");
        aaa = aaa.tab_bar_position(match position {
            TabBarPosition::Top => iced_aw::TabBarPosition::Top,
            TabBarPosition::Bottom => iced_aw::TabBarPosition::Bottom,
        });
        println!("1");
        aaa.into()

        // Tabs::new(self.active_tab, Message::TabSelected)
        //     .push(self.overview_tab.tab_label(), self.overview_tab.view())
        //     .push(
        //         self.send_and_receive_tab.tab_label(),
        //         self.send_and_receive_tab.view(),
        //     )
        //     .push(self.trade_tab.tab_label(), self.trade_tab.view())
        //     .push(self.settings_tab.tab_label(), self.settings_tab.view())
        //     .tab_bar_style(theme)
        //     .icon_font(ICON_FONT)
        //     .tab_bar_position(match position {
        //         TabBarPosition::Top => iced_aw::TabBarPosition::Top,
        //         TabBarPosition::Bottom => iced_aw::TabBarPosition::Bottom,
        //     })
        //     .into()
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

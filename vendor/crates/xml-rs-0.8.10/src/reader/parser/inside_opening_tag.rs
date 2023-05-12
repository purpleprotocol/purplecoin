use crate::reader::error::SyntaxError;
use crate::common::is_name_start_char;
use crate::namespace;
use crate::{attribute::OwnedAttribute, common::is_whitespace_char};

use crate::reader::lexer::Token;

use super::{OpeningTagSubstate, PullParser, QualifiedNameTarget, Result, State};

impl PullParser {
    pub fn inside_opening_tag(&mut self, t: Token, s: OpeningTagSubstate) -> Option<Result> {
        match s {
            OpeningTagSubstate::InsideName => self.read_qualified_name(t, QualifiedNameTarget::OpeningTagNameTarget, |this, token, name| {
                match name.prefix_ref() {
                    Some(prefix) if prefix == namespace::NS_XML_PREFIX ||
                                    prefix == namespace::NS_XMLNS_PREFIX =>
                        Some(this.error(SyntaxError::InvalidNamePrefix(prefix.into()))),
                    _ => {
                        this.data.element_name = Some(name.clone());
                        match token {
                            Token::TagEnd => this.emit_start_element(false),
                            Token::EmptyTagEnd => this.emit_start_element(true),
                            Token::Character(c) if is_whitespace_char(c) => this.into_state_continue(State::InsideOpeningTag(OpeningTagSubstate::InsideTag)),
                            _ => unreachable!()
                        }
                    }
                }
            }),

            OpeningTagSubstate::InsideTag => match t {
                Token::TagEnd => self.emit_start_element(false),
                Token::EmptyTagEnd => self.emit_start_element(true),
                Token::Character(c) if is_whitespace_char(c) => None,  // skip whitespace
                Token::Character(c) if is_name_start_char(c) => {
                    self.buf.push(c);
                    self.into_state_continue(State::InsideOpeningTag(OpeningTagSubstate::InsideAttributeName))
                }
                _ => Some(self.error(SyntaxError::UnexpectedTokenInOpeningTag(t)))
            },

            OpeningTagSubstate::InsideAttributeName => self.read_qualified_name(t, QualifiedNameTarget::AttributeNameTarget, |this, token, name| {
                this.data.attr_name = Some(name);
                match token {
                    Token::EqualsSign => this.into_state_continue(State::InsideOpeningTag(OpeningTagSubstate::InsideAttributeValue)),
                    Token::Character(c) if is_whitespace_char(c) => this.into_state_continue(State::InsideOpeningTag(OpeningTagSubstate::AfterAttributeName)),
                    _ => unreachable!()
                }
            }),

            OpeningTagSubstate::AfterAttributeName => match t {
                Token::EqualsSign => self.into_state_continue(State::InsideOpeningTag(OpeningTagSubstate::InsideAttributeValue)),
                Token::Character(c) if is_whitespace_char(c) => None,
                _ => Some(self.error(SyntaxError::UnexpectedTokenInOpeningTag(t)))
            },

            OpeningTagSubstate::InsideAttributeValue => self.read_attribute_value(t, |this, value| {
                let name = this.data.take_attr_name()?;  // will always succeed here
                // check that no attribute with such name is already present
                // if there is one, XML is not well-formed
                if this.data.attributes.iter().any(|a| a.name == name) {  // TODO: looks bad
                    // TODO: ideally this error should point to the beginning of the attribute,
                    // TODO: not the end of its value
                    Some(this.error(SyntaxError::RedefinedAttribute(name.to_string().into())))
                } else {
                    match name.prefix_ref() {
                        // declaring a new prefix; it is sufficient to check prefix only
                        // because "xmlns" prefix is reserved
                        Some(namespace::NS_XMLNS_PREFIX) => {
                            let ln = &*name.local_name;
                            if ln == namespace::NS_XMLNS_PREFIX {
                                Some(this.error(SyntaxError::CannotRedefineXmlnsPrefix))
                            } else if ln == namespace::NS_XML_PREFIX && &*value != namespace::NS_XML_URI {
                                Some(this.error(SyntaxError::CannotRedefineXmlPrefix))
                            } else if value.is_empty() {
                                Some(this.error(SyntaxError::CannotUndefinePrefix(ln.into())))
                            } else {
                                this.nst.put(name.local_name.clone(), value);
                                this.into_state_continue(State::InsideOpeningTag(OpeningTagSubstate::InsideTag))
                            }
                        }

                        // declaring default namespace
                        None if &*name.local_name == namespace::NS_XMLNS_PREFIX =>
                            match &*value {
                                namespace::NS_XMLNS_PREFIX | namespace::NS_XML_PREFIX | namespace::NS_XML_URI | namespace::NS_XMLNS_URI =>
                                    Some(this.error(SyntaxError::InvalidDefaultNamespace(value.into()))),
                                _ => {
                                    this.nst.put(namespace::NS_NO_PREFIX, value.clone());
                                    this.into_state_continue(State::InsideOpeningTag(OpeningTagSubstate::InsideTag))
                                }
                            },

                        // regular attribute
                        _ => {
                            this.data.attributes.push(OwnedAttribute {
                                name: name.clone(),
                                value
                            });
                            this.into_state_continue(State::InsideOpeningTag(OpeningTagSubstate::InsideTag))
                        }
                    }
                }
            })
        }
    }
}

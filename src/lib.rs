//! Core data types and whatnot for cetkaik, a board game. See <https://sites.google.com/view/cet2kaik/the-standardized-rule-in-english> for more context.
//! ／机戦（セットカイク）のための基本的なデータ型など。
#![warn(clippy::pedantic, clippy::nursery, missing_docs)]
#![allow(
    clippy::non_ascii_literal,
    clippy::use_self,
    clippy::upper_case_acronyms
)]
#[macro_use]
extern crate maplit;
/// Denotes the color of a piece／駒の色を表す。
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum Color {
    /// Red, 赤
    Kok1,

    /// Black, 黒
    Huok2,
}

/// Serializes [`Color`](./enum.Color.html).／[`Color`](./enum.Color.html)を文字列に変換する。
/// # Examples
/// ```
/// use cetkaik_core::*;
///
/// assert_eq!(serialize_color(Color::Kok1), "赤");
/// assert_eq!(serialize_color(Color::Huok2), "黒");
/// ```
///
#[must_use]
pub const fn serialize_color(color: Color) -> &'static str {
    match color {
        Color::Huok2 => "黒",
        Color::Kok1 => "赤",
    }
}

/// Denotes the profession of a piece／駒の職業を表す。
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum Profession {
    /// Vessel, 船, felkana
    Nuak1,

    /// Pawn, 兵, elmer
    Kauk2,

    /// Rook, 弓, gustuer
    Gua2,

    /// Bishop, 車, vadyrd
    Kaun1,

    /// Tiger, 虎, stistyst
    Dau2,

    /// Horse, 馬, dodor
    Maun1,

    /// Clerk, 筆, kua
    Kua2,

    /// Shaman, 巫, terlsk
    Tuk2,

    /// General, 将, varxle
    Uai1,

    /// King, 王, ales
    Io,
}

/// Serializes [`Profession`](./enum.Profession.html).／[`Profession`](./enum.Profession.html)を文字列にする。
/// # Examples
/// ```
/// use cetkaik_core::*;
///
/// assert_eq!(serialize_prof(Profession::Nuak1), "船");
/// assert_eq!(serialize_prof(Profession::Kaun1), "車");
/// ```
///
#[must_use]
pub const fn serialize_prof(prof: Profession) -> &'static str {
    match prof {
        Profession::Nuak1 => "船",
        Profession::Kauk2 => "兵",
        Profession::Gua2 => "弓",
        Profession::Kaun1 => "車",
        Profession::Dau2 => "虎",
        Profession::Maun1 => "馬",
        Profession::Kua2 => "筆",
        Profession::Tuk2 => "巫",
        Profession::Uai1 => "将",
        Profession::Io => "王",
    }
}

use std::str::FromStr;
impl FromStr for Profession {
    type Err = ();

    /// Parses [`Profession`](./enum.Profession.html).
    /// ／文字列を[`Profession`](./enum.Profession.html)にする。簡体字やリパライン語名などにも対応。
    /// # Examples
    /// ```
    /// use cetkaik_core::*;
    ///
    /// assert_eq!("船".parse(), Ok(Profession::Nuak1));
    /// assert_eq!("elmer".parse(), Ok(Profession::Kauk2));
    /// assert_eq!("车".parse(), Ok(Profession::Kaun1));
    /// assert_eq!("uai1".parse(), Ok(Profession::Uai1));
    /// ```
    ///
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_lowercase();
        match &*s {
            "vessel" | "船" | "felkana" | "nuak1" | "muak1" | "pelkana" | "pijume" | "muak" => {
                Ok(Profession::Nuak1)
            }
            "pawn" | "兵" | "elmer" | "kauk2" | "elme" | "kauk" => Ok(Profession::Kauk2),
            "rook" | "弓" | "gustuer" | "gua2" | "kucte" | "kuctu" => Ok(Profession::Gua2),
            "bishop" | "車" | "车" | "vadyrd" | "kaun1" | "badut" | "xije" | "kaun" => {
                Ok(Profession::Kaun1)
            }
            "tiger" | "虎" | "stistyst" | "dau2" | "cictus" | "cucit" | "dau" => {
                Ok(Profession::Dau2)
            }
            "horse" | "馬" | "马" | "dodor" | "maun1" | "dodo" | "maun" => Ok(Profession::Maun1),
            "clerk" | "筆" | "笔" | "kua" | "kua2" | "kuwa" => Ok(Profession::Kua2),
            "shaman" | "巫" | "terlsk" | "tuk2" | "tamcuk" | "tancuk" => Ok(Profession::Tuk2),
            "general" | "将" | "varxle" | "uai1" | "baxule" | "xan" | "wai" => {
                Ok(Profession::Uai1)
            }
            "king" | "王" | "ales" | "io" | "xet" | "caupla" => Ok(Profession::Io),
            _ => Err(()),
        }
    }
}

impl FromStr for Color {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_lowercase();
        match &*s {
            "red" | "赤" | "kok1" | "红" | "紅" => Ok(Color::Kok1),
            "black" | "黒" | "huok2" | "黑" => Ok(Color::Huok2),
            _ => Err(()),
        }
    }
}

/// Defines things in terms of relative view: "which piece is opponent's?"／相対座標ベース。「どの駒が相手の駒？」という話をする
pub mod relative;

/// Defines things in the absolute term: "which piece lies in the square LIA?"／絶対座標ベース。「LIAのマスにはどの駒がある？」という話をする
pub mod absolute;

/// Defines a perspective, with which you can transform between the absolute and the relative／視点を定めることで、相対座標と絶対座標の間を変換できるようにする
pub mod perspective;

impl serde::ser::Serialize for Color {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        serializer.serialize_str(serialize_color(*self))
    }
}

impl serde::ser::Serialize for Profession {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        serializer.serialize_str(serialize_prof(*self))
    }
}

struct ColorVisitor;

impl<'de> serde::de::Visitor<'de> for ColorVisitor {
    type Value = Color;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a color")
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Color::from_str(s).map_or_else(
            |_| {
                Err(serde::de::Error::invalid_value(
                    serde::de::Unexpected::Str(s),
                    &self,
                ))
            },
            |c| Ok(c),
        )
    }
}

impl<'de> serde::de::Deserialize<'de> for Color {
    fn deserialize<D>(deserializer: D) -> Result<Color, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        deserializer.deserialize_str(ColorVisitor)
    }
}

struct ProfessionVisitor;

impl<'de> serde::de::Visitor<'de> for ProfessionVisitor {
    type Value = Profession;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a profession")
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Profession::from_str(s).map_or_else(
            |_| {
                Err(serde::de::Error::invalid_value(
                    serde::de::Unexpected::Str(s),
                    &self,
                ))
            },
            |c| Ok(c),
        )
    }
}

impl<'de> serde::de::Deserialize<'de> for Profession {
    fn deserialize<D>(deserializer: D) -> Result<Profession, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        deserializer.deserialize_str(ProfessionVisitor)
    }
}

/// A shortcut macro for creating `ColorAndProf`, which is essentially a tuple of the color and the profession.
/// ／`ColorAndProf` を楽に構築するためのマクロ。
///
/// # Example
/// ```
/// use cetkaik_core::{cp, color, prof, ColorAndProf, Color, Profession};
/// use cetkaik_core::Color::*;
/// use cetkaik_core::Profession::*;
/// assert_eq!(cp!('赤', '兵'), ColorAndProf { color: Kok1, prof: Kauk2 });
/// assert_eq!(cp!('黒', '船'), ColorAndProf { color: Huok2, prof: Nuak1 });
/// ```
#[macro_export]
macro_rules! cp {
    ($c:tt, $p:tt) => {
        ColorAndProf {
            prof: prof!($p),
            color: color!($c),
        }
    };
}

/// A shortcut macro for creating `Profession`.
/// ／`Profession` を楽に構築するためのマクロ。
#[macro_export]
macro_rules! prof {
    ('船') => {
        Profession::Nuak1
    };

    ('兵') => {
        Profession::Kauk2
    };

    ('弓') => {
        Profession::Gua2
    };

    ('車') => {
        Profession::Kaun1
    };

    ('虎') => {
        Profession::Dau2
    };

    ('馬') => {
        Profession::Maun1
    };

    ('筆') => {
        Profession::Kua2
    };

    ('巫') => {
        Profession::Tuk2
    };

    ('将') => {
        Profession::Uai1
    };

    ('王') => {
        Profession::Io
    };
}

/// A shortcut macro for creating `Color`.
/// ／`Color` を楽に構築するためのマクロ。
#[macro_export]
macro_rules! color {
    ('黒') => {
        Color::Huok2
    };
    ('赤') => {
        Color::Kok1
    };
}

/// Describes a move.
/// ／指した手を表す。
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PureMove_<Coord> {
    /// A non-Tam2 piece moves from a square on a board to another square without stepping.
    /// ／皇ではない駒が、盤上から盤上に踏越えなしで移動する。
    NonTamMoveSrcDst {
        /// origin／開始点
        src: Coord,
        /// final destination／終了点
        dest: Coord,
        /// whether a water-entry ciurl is required／入水判定が必要かどうか
        is_water_entry_ciurl: bool,
    },
    /// A non-Tam2 piece moves from a square on a board to another square, during which it steps another piece and does a finite movement.
    /// ／皇ではない駒が、盤上から盤上に踏越えを伴いながら移動し、踏越え後は有限移動をする。
    NonTamMoveSrcStepDstFinite {
        /// origin／開始点
        src: Coord,
        /// via point／経由点
        step: Coord,
        /// destination／終了点
        dest: Coord,
        /// whether a water-entry ciurl is required／入水判定が必要かどうか
        is_water_entry_ciurl: bool,
    },
    /// A non-Tam2 piece moves from a square on a board to another square, during which it steps another piece and tries to do a directional, infinite movement.
    /// ／皇ではない駒が、盤上から盤上に踏越えを伴いながら移動し、踏越え後は無限移動をしようとする。
    InfAfterStep {
        /// origin／開始点
        src: Coord,
        /// via point／経由点
        step: Coord,
        /// the planned LOCATION. After casting the sticks, some rules necessitates that you go to the destination or to the direction that you have declared beforehand.
        /// Hence the confusing name.
        /// ／行く予定の場所。踏越え判定後の移動先は、ルールによっては「計画したマス」である必要があったり「計画した方角」である必要があったりする。
        planned_direction: Coord,
    },
    /// A non-Tam2 piece moves from hop1zuo1 to a square on a board.
    /// ／皇ではない駒が、手駒から盤上に移動する。
    NonTamMoveFromHopZuo {
        /// color／駒の色
        color: Color,
        /// profession／駒の役職
        prof: Profession,
        /// destination／終了点
        dest: Coord,
    },
    /// A Tam2 moves from a square on a board to another square without stepping.
    /// ／皇が盤上から盤上に踏越えなしで移動する。
    TamMoveNoStep {
        /// origin／開始点
        src: Coord,
        /// first destination／一回目の終了点
        first_dest: Coord,
        /// second destination／二回目の終了点
        second_dest: Coord,
    },
    /// A Tam2 moves from a square on a board to another square. In the former half of its movement, it steps another piece.
    /// ／皇が盤上から盤上に移動し、一回目の移動の最中に踏越えをする。
    TamMoveStepsDuringFormer {
        /// origin／開始点
        src: Coord,
        /// via point／経由点
        step: Coord,
        /// first destination／一回目の終了点
        first_dest: Coord,
        /// second destination／二回目の終了点
        second_dest: Coord,
    },
    /// A Tam2 moves from a square on a board to another square. In the latter half of its movement, it steps another piece.
    /// ／皇が盤上から盤上に移動し、二回目の移動の最中に踏越えをする。
    TamMoveStepsDuringLatter {
        /// origin／開始点
        src: Coord,
        /// via point／経由点
        step: Coord,
        /// first destination／一回目の終了点
        first_dest: Coord,
        /// second destination／二回目の終了点
        second_dest: Coord,
    },
}

/// Describes a piece that is not a Tam2, and hence can be taken and be placed in a hop1zuo1.
/// ／駒のうち、皇以外を表す。これは手駒として存在できる駒でもある。
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Deserialize, Serialize)]
pub struct ColorAndProf {
    /// color of the piece／駒の色
    pub color: Color,
    /// profession of the piece／駒の職種
    pub prof: Profession,
}

impl std::fmt::Display for ColorAndProf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            serialize_color(self.color),
            serialize_prof(self.prof)
        )
    }
}
use std::convert::TryInto;

use serde::{Deserialize, Serialize};
impl TryInto<ColorAndProf> for &str {
    type Error = ();
    fn try_into(self) -> Result<ColorAndProf, Self::Error> {
        Ok(match self {
            "黒兵" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Kauk2,
            },
            "赤兵" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Kauk2,
            },
            "黒弓" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Gua2,
            },
            "黒車" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Kaun1,
            },
            "黒虎" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Dau2,
            },
            "黒馬" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Maun1,
            },
            "黒筆" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Kua2,
            },
            "黒巫" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Tuk2,
            },
            "黒将" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Uai1,
            },
            "赤弓" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Gua2,
            },
            "赤車" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Kaun1,
            },
            "赤虎" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Dau2,
            },
            "赤馬" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Maun1,
            },
            "赤筆" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Kua2,
            },
            "赤巫" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Tuk2,
            },
            "赤将" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Uai1,
            },
            "黒王" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Io,
            },
            "赤王" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Io,
            },
            "黒船" => ColorAndProf {
                color: Color::Huok2,
                prof: Profession::Nuak1,
            },
            "赤船" => ColorAndProf {
                color: Color::Kok1,
                prof: Profession::Nuak1,
            },
            _ => return Err(()),
        })
    }
}

/// A trait that signifies that you can use it as a `Board` with an absolute coordinate
/// ／絶対座標付きの `Board` として扱える型を表すトレイト
pub trait IsAbsoluteBoard: IsBoard {
/// The initial arrangement of the official (yhuap) rule
    fn yhuap_initial() -> Self;
}

/// A trait that signifies that you can use it as a `Board`
/// ／`Board` として扱える型を表すトレイト
pub trait IsBoard {
    /// A type that represents the piece
    type PieceWithSide: Copy;
    /// A type that represents the coordinate
    type Coord: Copy + std::fmt::Debug;
    
    /// peek
    fn peek(&self, c: Self::Coord) -> Option<Self::PieceWithSide>;
    /// pop
    fn pop(&mut self, c: Self::Coord) -> Option<Self::PieceWithSide>;
    /// put either a piece or a `None`
    fn put(&mut self, c: Self::Coord, p: Option<Self::PieceWithSide>);
    /// assert that the square is empty
    fn assert_empty(&self, c: Self::Coord);
    /// assert that the square is occupied
    fn assert_occupied(&self, c: Self::Coord);
    /// Moves the piece located at `from` to an empty square `to`.
    /// # Panics
    /// Should panics if either:
    /// - `from` is unoccupied
    /// - `to` is already occupied
    fn mov(&mut self, from: Self::Coord, to: Self::Coord) {
        self.pop(from).map_or_else(
            || panic!("Empty square encountered at {from:?}"),
            |src_piece| {
                self.assert_empty(to);
                self.put(to, Some(src_piece));
            },
        );
    }
}

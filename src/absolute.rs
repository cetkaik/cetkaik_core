use super::{Color, Profession};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

/// Describes a piece on the board.
/// ／盤上に存在できる駒を表現する。
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Deserialize, Serialize)]
pub enum Piece {
    /// Tam2, a special piece belonging to both sides. Both players can move it.
    /// ／皇（たむ）。自分も相手も動かすことができる共有の駒である。
    Tam2,

    /// All the other usual pieces that belong to a single side.
    /// ／残りの全ての普通の駒。片方の陣営にのみ属する。
    NonTam2Piece {
        /// color of the piece／駒の色
        color: Color,
        /// profession of the piece／駒の職種
        prof: Profession,

        /// which side the piece belongs to
        /// ／駒の所属側。どちらの陣営に属しているのかを表す。
        side: Side,
    },
}

/// Calculates the distance between two points.
/// The distance is defined as the larger of the difference between either the x or y coordinates.
/// ／2点間の距離（x座標の差およびy座標の差のうち小さくない方）を計算する。
///
/// Examples:
/// ```
/// use cetkaik_core::absolute::{distance, Coord};
/// use cetkaik_core::absolute::Row::*;
/// use cetkaik_core::absolute::Column::*;
///
/// assert_eq!(2, distance(Coord(A, K), Coord(I, N)));
/// assert_eq!(2, distance(Coord(I, K), Coord(I, N)));
///
/// // The standard cetkaik does not care about knight's moves, but is tested for the sake of consistency.
/// assert_eq!(2, distance(Coord(A, K), Coord(E, N)));
/// ```
#[must_use]
pub fn distance(a: Coord, b: Coord) -> i32 {
    use super::{perspective, relative};
    // coordinate-independent, so I can just choose one
    relative::distance(
        perspective::to_relative_coord(a, perspective::Perspective::IaIsDownAndPointsUpward),
        perspective::to_relative_coord(b, perspective::Perspective::IaIsDownAndPointsUpward),
    )
}

impl Piece {
    /// Checks whether the piece is a Tam2.
    /// ／皇であるかどうかの判定
    #[must_use]
    pub const fn is_tam2(self) -> bool {
        match self {
            Piece::Tam2 => true,
            Piece::NonTam2Piece { .. } => false,
        }
    }

    /// Checks whether the piece has a specific color. Tam2 has neither color.
    /// ／駒が特定の色であるかを調べる。皇は赤でも黒でもない。
    #[must_use]
    pub fn has_color(self, clr: Color) -> bool {
        match self {
            Piece::Tam2 => false,
            Piece::NonTam2Piece { color, .. } => color == clr,
        }
    }

    /// Checks whether the piece has a specific profession.
    /// ／駒が特定の職種であるかを調べる。
    #[must_use]
    pub fn has_prof(self, prf: Profession) -> bool {
        match self {
            Piece::Tam2 => false,
            Piece::NonTam2Piece { prof, .. } => prof == prf,
        }
    }

    /// Checks whether the piece belongs to a specific side. Tam2 belongs to neither side.
    /// ／駒が特定の側のプレイヤーに属するかどうかを調べる。皇はどちらの陣営にも属さない。
    #[must_use]
    pub fn has_side(self, sid: Side) -> bool {
        match self {
            Piece::Tam2 => false,
            Piece::NonTam2Piece { side, .. } => side == sid,
        }
    }
}

/// Checks if the square is a tam2 nua2 (tam2's water), entry to which is restricted.
/// ／マスが皇水（たむぬあ）であるかどうかの判定
#[must_use]
pub const fn is_water(Coord(row, col): Coord) -> bool {
    match row {
        Row::O => matches!(
            col,
            Column::N | Column::T | Column::Z | Column::X | Column::C
        ),
        Row::I | Row::U | Row::Y | Row::AI => matches!(col, Column::Z),
        _ => false,
    }
}

/// Describes a piece that is not a Tam2, and hence can be taken and be placed in a hop1zuo1.
/// ／駒のうち、皇以外を表す。これは手駒として存在できる駒でもある。
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Deserialize, Serialize)]
pub struct NonTam2Piece {
    /// color of the piece／駒の色
    pub color: Color,
    /// profession of the piece／駒の職種
    pub prof: Profession,
}

impl std::fmt::Display for NonTam2Piece {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            super::serialize_color(self.color),
            super::serialize_prof(self.prof)
        )
    }
}
use std::convert::TryInto;
impl TryInto<NonTam2Piece> for &str {
    type Error = ();
    fn try_into(self) -> Result<NonTam2Piece, Self::Error> {
        Ok(match self {
            "黒兵" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
            },
            "赤兵" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
            },
            "黒弓" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Gua2,
            },
            "黒車" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kaun1,
            },
            "黒虎" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Dau2,
            },
            "黒馬" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Maun1,
            },
            "黒筆" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kua2,
            },
            "黒巫" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Tuk2,
            },
            "黒将" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Uai1,
            },
            "赤弓" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Gua2,
            },
            "赤車" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kaun1,
            },
            "赤虎" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Dau2,
            },
            "赤馬" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Maun1,
            },
            "赤筆" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kua2,
            },
            "赤巫" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Tuk2,
            },
            "赤将" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Uai1,
            },
            "黒王" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Io,
            },
            "赤王" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Io,
            },
            "黒船" => NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Nuak1,
            },
            "赤船" => NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Nuak1,
            },
            _ => return Err(()),
        })
    }
}

use std::collections::HashMap;

/// Describes the board, the 9x9 squares, in terms of absolute coordinates.
/// ／盤、つまり、9x9のマス目を、絶対座標で表す。
pub type Board = HashMap<Coord, Piece>;

/// Describes the field, which is defined as a board plus each side's hop1zuo1.
/// ／フィールドを表す。フィールドとは、盤に両者の手駒を加えたものである。
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Field {
    /// board／盤
    pub board: Board,

    /// hop1zuo1 for the ASide／A側の手駒
    pub a_side_hop1zuo1: Vec<NonTam2Piece>,

    /// hop1zuo1 for the IASide／IA側の手駒
    pub ia_side_hop1zuo1: Vec<NonTam2Piece>,
}

impl Field {
    /// Add a piece to one's hop1zuo1.
    /// ／手駒に駒を追加する。
    pub fn insert_nontam_piece_into_hop1zuo1(
        &mut self,
        color: Color,
        prof: Profession,
        side: Side,
    ) {
        match side {
            Side::ASide => self.a_side_hop1zuo1.push(NonTam2Piece { color, prof }),
            Side::IASide => self.ia_side_hop1zuo1.push(NonTam2Piece { color, prof }),
        }
    }

    /// Remove a specified piece from one's hop1zuo1; if none is found, return `None`.
    /// ／手駒から指定の駒を削除する。見当たらないなら `None`。
    #[must_use]
    pub fn find_and_remove_piece_from_hop1zuo1(
        &self,
        color: Color,
        prof: Profession,
        side: Side,
    ) -> Option<Self> {
        match side {
            Side::ASide => {
                let mut that = self.clone();
                let index = that
                    .a_side_hop1zuo1
                    .iter()
                    .position(|x| *x == NonTam2Piece { color, prof })?;
                that.a_side_hop1zuo1.remove(index);
                Some(that)
            }
            Side::IASide => {
                let mut that = self.clone();
                let index = that
                    .ia_side_hop1zuo1
                    .iter()
                    .position(|x| *x == NonTam2Piece { color, prof })?;
                that.ia_side_hop1zuo1.remove(index);
                Some(that)
            }
        }
    }
}

/// Describes which player it is
/// ／どちら側のプレイヤーであるかを指定する。
#[derive(Eq, PartialEq, Clone, Copy, Debug, Hash, Deserialize, Serialize)]
pub enum Side {
    /// The player whose pieces lie in the A, E and I row when the game starts.
    /// ／A側プレイヤー。初期状態でA, E, Iの三列に渡って自分の駒が配置されている。
    ASide,

    /// The player whose pieces lie in the IA, AU and AI row when the game starts.
    /// ／IA側プレイヤー。初期状態でIA, AU, AIの三列に渡って自分の駒が配置されている。
    IASide,
}

impl FromStr for Side {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "A" => Ok(Side::ASide),
            "IA" => Ok(Side::IASide),
            _ => Err(()),
        }
    }
}

use std::ops;
impl ops::Not for Side {
    type Output = Side;

    fn not(self) -> Self::Output {
        match self {
            Side::ASide => Side::IASide,
            Side::IASide => Side::ASide,
        }
    }
}

/// Describes the row.
/// ／盤上の絶対座標のうち行（横列）を表す。
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Deserialize, Serialize)]
#[allow(missing_docs)]
pub enum Row {
    A,
    E,
    I,
    U,
    O,
    Y,
    AI,
    AU,
    IA,
}

/// Describes the column.
/// ／盤上の絶対座標のうち列（縦列）を表す。
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Deserialize, Serialize)]
#[allow(missing_docs)]
pub enum Column {
    K,
    L,
    N,
    T,
    Z,
    X,
    C,
    M,
    P,
}

/// Describes the absolute coordinate.
/// ／盤上の絶対座標を表す。
#[derive(Clone, Debug, Eq, Hash, PartialEq, Copy)]
pub struct Coord(pub Row, pub Column);

impl serde::ser::Serialize for Coord {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        serializer.serialize_str(&serialize_coord(*self))
    }
}

struct CoordVisitor;

impl<'de> serde::de::Visitor<'de> for CoordVisitor {
    type Value = Coord;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a coordinate")
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        match Coord::from_str(s) {
            Ok(c) => Ok(c),
            Err(_) => Err(serde::de::Error::invalid_value(
                serde::de::Unexpected::Str(s),
                &self,
            )),
        }
    }
}

impl<'de> serde::de::Deserialize<'de> for Coord {
    fn deserialize<D>(deserializer: D) -> Result<Coord, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        deserializer.deserialize_str(CoordVisitor)
    }
}

impl FromStr for Coord {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_coord(s).ok_or(())
    }
}

/// Parses [`Coord`](type.Coord.html). ／ 文字列を[`Coord`](type.Coord.html)にする。
/// # Examples
/// ```
/// use cetkaik_core::absolute::*;
/// assert_eq!(
///     parse_coord("LIA"),
///     Some(Coord(Row::IA, Column::L))
/// );
///
/// // case-sensitive
/// assert_eq!(
///     parse_coord("LiA"),
///     None
/// );
/// ```
#[must_use]
pub fn parse_coord(coord: &str) -> Option<Coord> {
    if coord.is_empty() || coord.len() > 3 {
        return None;
    }

    let column = match coord.chars().next() {
        Some('C') => Some(Column::C),
        Some('K') => Some(Column::K),
        Some('L') => Some(Column::L),
        Some('M') => Some(Column::M),
        Some('N') => Some(Column::N),
        Some('P') => Some(Column::P),
        Some('T') => Some(Column::T),
        Some('X') => Some(Column::X),
        Some('Z') => Some(Column::Z),
        None | Some(_) => None,
    }?;

    let row = match &coord[1..coord.len()] {
        "A" => Some(Row::A),
        "AI" => Some(Row::AI),
        "AU" => Some(Row::AU),
        "E" => Some(Row::E),
        "I" => Some(Row::I),
        "O" => Some(Row::O),
        "U" => Some(Row::U),
        "Y" => Some(Row::Y),
        "IA" => Some(Row::IA),
        _ => None,
    }?;

    Some(Coord(row, column))
}

/// Returns the initial configuration as specified in the y1 huap1 (the standardized rule).
/// As can be seen in <https://raw.githubusercontent.com/sozysozbot/cerke/master/y1_huap1_summary_en.pdf>,
/// a black king is in ZIA while a red king is in ZA.
/// ／官定で定められた初期配置を与える。
/// <https://raw.githubusercontent.com/sozysozbot/cerke/master/y1_huap1_summary.pdf> にあるように、
/// ZIAには黒王、ZAには赤王がある。
/// 
/// # Examples
/// ```
/// use cetkaik_core::absolute::{yhuap_initial_board, Row, Column, Coord, Piece, Side};
/// use cetkaik_core::{Color, Profession};
/// assert_eq!(Some(&Piece::Tam2), yhuap_initial_board().get(&Coord(Row::O, Column::Z)));
/// assert_eq!(
///     &Piece::NonTam2Piece {prof: Profession::Io, color: Color::Huok2, side: Side::IASide},
///     yhuap_initial_board().get(&Coord(Row::IA, Column::Z)).unwrap()
/// )
/// ```
/// 
/// This function is consistent with `relative::yhuap_initial_board_where_black_king_points_upward`:
/// 
/// ```
/// use cetkaik_core::{absolute, relative, perspective};
/// assert_eq!(perspective::to_absolute_board(
///     &relative::yhuap_initial_board_where_black_king_points_upward(),
///     perspective::Perspective::IaIsDownAndPointsUpward
/// ), absolute::yhuap_initial_board())
/// ```
#[must_use]
pub fn yhuap_initial_board() -> Board {
    hashmap! {
        Coord(Row::O, Column::Z) => Piece::Tam2,
        Coord(Row::AI, Column::Z) => Piece::NonTam2Piece {prof: Profession::Nuak1, color: Color::Huok2, side: Side::IASide},
        Coord(Row::AI, Column::K) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Huok2, side: Side::IASide},
        Coord(Row::AI, Column::N) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Huok2, side: Side::IASide},
        Coord(Row::AI, Column::C) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Huok2, side: Side::IASide},
        Coord(Row::AI, Column::P) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Huok2, side: Side::IASide},
        Coord(Row::AI, Column::L) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Kok1, side: Side::IASide},
        Coord(Row::AI, Column::T) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Kok1, side: Side::IASide},
        Coord(Row::AI, Column::X) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Kok1, side: Side::IASide},
        Coord(Row::AI, Column::M) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Kok1, side: Side::IASide},
        Coord(Row::AU, Column::L) => Piece::NonTam2Piece {prof: Profession::Gua2, color: Color::Huok2, side: Side::IASide},
        Coord(Row::AU, Column::M) => Piece::NonTam2Piece {prof: Profession::Gua2, color: Color::Kok1, side: Side::IASide},
        Coord(Row::IA, Column::C) => Piece::NonTam2Piece {prof: Profession::Kaun1, color: Color::Huok2, side: Side::IASide},
        Coord(Row::IA, Column::N) => Piece::NonTam2Piece {prof: Profession::Kaun1, color: Color::Kok1, side: Side::IASide},
        Coord(Row::AU, Column::T) => Piece::NonTam2Piece {prof: Profession::Dau2, color: Color::Huok2, side: Side::IASide},
        Coord(Row::AU, Column::X) => Piece::NonTam2Piece {prof: Profession::Dau2, color: Color::Kok1, side: Side::IASide},
        Coord(Row::IA, Column::M) => Piece::NonTam2Piece {prof: Profession::Maun1, color: Color::Huok2, side: Side::IASide},
        Coord(Row::IA, Column::L) => Piece::NonTam2Piece {prof: Profession::Maun1, color: Color::Kok1, side: Side::IASide},
        Coord(Row::IA, Column::P) => Piece::NonTam2Piece {prof: Profession::Kua2, color: Color::Huok2, side: Side::IASide},
        Coord(Row::AU, Column::P) => Piece::NonTam2Piece {prof: Profession::Tuk2, color: Color::Kok1, side: Side::IASide},
        Coord(Row::IA, Column::X) => Piece::NonTam2Piece {prof: Profession::Uai1, color: Color::Huok2, side: Side::IASide},
        Coord(Row::IA, Column::T) => Piece::NonTam2Piece {prof: Profession::Uai1, color: Color::Kok1, side: Side::IASide},
        Coord(Row::IA, Column::Z) => Piece::NonTam2Piece {prof: Profession::Io, color: Color::Huok2, side: Side::IASide},
        Coord(Row::IA, Column::K) => Piece::NonTam2Piece {prof: Profession::Kua2, color: Color::Kok1, side: Side::IASide},
        Coord(Row::AU, Column::K) => Piece::NonTam2Piece {prof: Profession::Tuk2, color: Color::Huok2, side: Side::IASide},
        Coord(Row::I, Column::Z) => Piece::NonTam2Piece {prof: Profession::Nuak1, color: Color::Kok1, side: Side::ASide},
        Coord(Row::I, Column::K) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Huok2, side: Side::ASide},
        Coord(Row::I, Column::N) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Huok2, side: Side::ASide},
        Coord(Row::I, Column::C) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Huok2, side: Side::ASide},
        Coord(Row::I, Column::P) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Huok2, side: Side::ASide},
        Coord(Row::I, Column::L) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Kok1, side: Side::ASide},
        Coord(Row::I, Column::T) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Kok1, side: Side::ASide},
        Coord(Row::I, Column::X) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Kok1, side: Side::ASide},
        Coord(Row::I, Column::M) => Piece::NonTam2Piece {prof: Profession::Kauk2, color: Color::Kok1, side: Side::ASide},
        Coord(Row::E, Column::M) => Piece::NonTam2Piece {prof: Profession::Gua2, color: Color::Huok2, side: Side::ASide},
        Coord(Row::E, Column::L) => Piece::NonTam2Piece {prof: Profession::Gua2, color: Color::Kok1, side: Side::ASide},
        Coord(Row::A, Column::N) => Piece::NonTam2Piece {prof: Profession::Kaun1, color: Color::Huok2, side: Side::ASide},
        Coord(Row::A, Column::C) => Piece::NonTam2Piece {prof: Profession::Kaun1, color: Color::Kok1, side: Side::ASide},
        Coord(Row::E, Column::X) => Piece::NonTam2Piece {prof: Profession::Dau2, color: Color::Huok2, side: Side::ASide},
        Coord(Row::E, Column::T) => Piece::NonTam2Piece {prof: Profession::Dau2, color: Color::Kok1, side: Side::ASide},
        Coord(Row::A, Column::L) => Piece::NonTam2Piece {prof: Profession::Maun1, color: Color::Huok2, side: Side::ASide},
        Coord(Row::A, Column::M) => Piece::NonTam2Piece {prof: Profession::Maun1, color: Color::Kok1, side: Side::ASide},
        Coord(Row::A, Column::K) => Piece::NonTam2Piece {prof: Profession::Kua2, color: Color::Huok2, side: Side::ASide},
        Coord(Row::E, Column::P) => Piece::NonTam2Piece {prof: Profession::Tuk2, color: Color::Huok2, side: Side::ASide},
        Coord(Row::A, Column::P) => Piece::NonTam2Piece {prof: Profession::Kua2, color: Color::Kok1, side: Side::ASide},
        Coord(Row::E, Column::K) => Piece::NonTam2Piece {prof: Profession::Tuk2, color: Color::Kok1, side: Side::ASide},
        Coord(Row::A, Column::T) => Piece::NonTam2Piece {prof: Profession::Uai1, color: Color::Huok2, side: Side::ASide},
        Coord(Row::A, Column::X) => Piece::NonTam2Piece {prof: Profession::Uai1, color: Color::Kok1, side: Side::ASide},
        Coord(Row::A, Column::Z) => Piece::NonTam2Piece {prof: Profession::Io, color: Color::Kok1, side: Side::ASide},
    }
}

/// Serializes [`Coord`](../type.Coord.html).／[`Coord`](../type.Coord.html)を文字列にする。
/// # Examples
/// ```
/// use cetkaik_core::absolute::*;
///
/// assert_eq!(serialize_coord(Coord(Row::E, Column::N)), "NE");
/// assert_eq!(serialize_coord(Coord(Row::AU, Column::Z)), "ZAU");
/// ```
///
#[must_use]
pub fn serialize_coord(coord: Coord) -> String {
    let Coord(row, column) = coord;
    format!(
        "{}{}",
        match column {
            Column::K => "K",
            Column::L => "L",
            Column::M => "M",
            Column::N => "N",
            Column::P => "P",
            Column::Z => "Z",
            Column::X => "X",
            Column::C => "C",
            Column::T => "T",
        },
        match row {
            Row::A => "A",
            Row::E => "E",
            Row::I => "I",
            Row::O => "O",
            Row::U => "U",
            Row::Y => "Y",
            Row::IA => "IA",
            Row::AI => "AI",
            Row::AU => "AU",
        }
    )
}

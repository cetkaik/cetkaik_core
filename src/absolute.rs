use crate::ColorAndProf;

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

/// Checks whether `a` and `b` are in the same direction when measured from `origin`.
/// ／`origin` から見て `a`と`b`が同じ向きに位置しているかを返す。
///
/// Examples:
/// ```
/// use cetkaik_core::absolute::{same_direction, Coord};
/// use cetkaik_core::absolute::Row::*;
/// use cetkaik_core::absolute::Column::*;
///
/// assert_eq!(true, same_direction(Coord(IA, Z), Coord(A, Z), Coord(E, Z)));
/// assert_eq!(false, same_direction(Coord(IA, Z), Coord(A, P), Coord(E, Z)));
/// assert_eq!(false, same_direction(Coord(O, Z), Coord(A, Z), Coord(IA, Z)));
/// ```
#[must_use]
#[allow(clippy::cast_possible_wrap)]
pub const fn same_direction(origin: Coord, a: Coord, b: Coord) -> bool {
    use super::perspective;

    // coordinate-independent, so I can just choose one
    let origin =
        perspective::to_relative_coord(origin, perspective::Perspective::IaIsDownAndPointsUpward);
    let a = perspective::to_relative_coord(a, perspective::Perspective::IaIsDownAndPointsUpward);
    let b = perspective::to_relative_coord(b, perspective::Perspective::IaIsDownAndPointsUpward);

    let a_u = (a[0] as isize) - (origin[0] as isize);
    let a_v = (a[1] as isize) - (origin[1] as isize);
    let b_u = (b[0] as isize) - (origin[0] as isize);
    let b_v = (b[1] as isize) - (origin[1] as isize);

    (a_u * b_u + a_v * b_v > 0) && (a_u * b_v - a_v * b_u == 0)
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

impl crate::IsAbsoluteBoard for Board {
    fn yhuap_initial() -> Self {
        yhuap_initial_board()
    }
}

impl crate::IsBoard for Board {
    type PieceWithSide = Piece;

    type Coord = Coord;

    fn peek(&self, c: Self::Coord) -> Option<Self::PieceWithSide> {
        self.get(&c).copied()
    }

    fn pop(&mut self, c: Self::Coord) -> Option<Self::PieceWithSide> {
        self.remove(&c)
    }

    fn put(&mut self, c: Self::Coord, p: Option<Self::PieceWithSide>) {
        match p {
            None => {
                self.remove(&c);
            }
            Some(piece) => {
                self.insert(c, piece);
            }
        }
    }

    fn assert_empty(&self, c: Self::Coord) {
        assert!(
            !self.contains_key(&c),
            "Expected the square {:?} to be empty, but it was occupied",
            c
        );
    }

    fn assert_occupied(&self, c: Self::Coord) {
        assert!(
            self.contains_key(&c),
            "Expected the square {:?} to be occupied, but it was empty",
            c
        );
    }
}

impl crate::IsField for Field {
    type Board = Board;
    type Coord = Coord;
    type PieceWithSide = Piece;
    type Side = Side;

    fn move_nontam_piece_from_src_to_dest_while_taking_opponent_piece_if_needed(
        &self,
        src: Self::Coord,
        dest: Self::Coord,
        whose_turn: Self::Side,
    ) -> Result<Self, &'static str> {
        let mut new_self = self.clone();
        let src_piece = new_self
            .board
            .remove(&src)
            .ok_or("src does not contain a piece")?;

        let Piece::NonTam2Piece { color: _color, prof: _prof, side } = src_piece 
        else {
            return Err("Expected a NonTam2Piece to be present at the src, but found a Tam2")
        };

        if whose_turn != side {
            return Err("Found the opponent piece at the src");
        }

        let maybe_captured_piece = new_self.board.remove(&dest);
        new_self.board.insert(dest, src_piece);

        if let Some(captured_piece) = maybe_captured_piece {
            match captured_piece {
                Piece::Tam2 => return Err("Tried to capture a Tam2"),
                Piece::NonTam2Piece {
                    color: captured_piece_color,
                    prof: captured_piece_prof,
                    side: captured_piece_side,
                } => {
                    if captured_piece_side == whose_turn {
                        return Err("Tried to capture an ally");
                    }
                    match whose_turn {
                        Side::IASide => new_self.ia_side_hop1zuo1.push(crate::ColorAndProf {
                            color: captured_piece_color,
                            prof: captured_piece_prof,
                        }),
                        Side::ASide => new_self.a_side_hop1zuo1.push(crate::ColorAndProf {
                            color: captured_piece_color,
                            prof: captured_piece_prof,
                        }),
                    }
                }
            }
        }
        Ok(new_self)
    }

    fn as_board(&self) -> &Self::Board {
        &self.board
    }

    fn as_board_mut(&mut self) -> &mut Self::Board {
        &mut self.board
    }

    #[must_use]
    fn search_from_hop1zuo1_and_parachute_at(
        &self,
        color: Color,
        prof: Profession,
        side: Self::Side,
        to: Self::Coord,
    ) -> Option<Self> {
        match side {
            Side::ASide => {
                let mut new_self = self.clone();
                let index = new_self
                    .a_side_hop1zuo1
                    .iter()
                    .position(|x| *x == ColorAndProf { color, prof })?;
                new_self.a_side_hop1zuo1.remove(index);

                if self.board.contains_key(&to) {
                    return None;
                }

                new_self
                    .board
                    .insert(to, Piece::NonTam2Piece { color, prof, side });

                Some(new_self)
            }
            Side::IASide => {
                let mut new_self = self.clone();
                let index = new_self
                    .ia_side_hop1zuo1
                    .iter()
                    .position(|x| *x == ColorAndProf { color, prof })?;
                new_self.ia_side_hop1zuo1.remove(index);

                if self.board.contains_key(&to) {
                    return None;
                }
                new_self.board
                    .insert(to, Piece::NonTam2Piece { color, prof, side });

                Some(new_self)
            }
        }
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
    pub a_side_hop1zuo1: Vec<ColorAndProf>,

    /// hop1zuo1 for the IASide／IA側の手駒
    pub ia_side_hop1zuo1: Vec<ColorAndProf>,
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
            Side::ASide => self.a_side_hop1zuo1.push(ColorAndProf { color, prof }),
            Side::IASide => self.ia_side_hop1zuo1.push(ColorAndProf { color, prof }),
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
        Coord::from_str(s).map_or_else(
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

/// Describes a move denoted in absolute coordinates.
/// ／絶対座標で書かれた指し手を表す。
pub type PureMove = crate::PureMove_<Coord>;

impl PureMove {
    /// Serializes [`PureMove`](./enum.PureMove.html) in textual form.
    /// # Examples
    /// ```
    /// use cetkaik_core::*;
    /// use cetkaik_core::absolute::*;
    ///
    /// assert_eq!(PureMove::InfAfterStep {
    ///     src: Coord(Row::A, Column::Z),
    ///     step: Coord(Row::E, Column::T),
    ///     planned_direction: Coord(Row::E, Column::N)
    /// }.serialize(), "ZA片TE心NE");
    ///
    /// assert_eq!(PureMove::NonTamMoveFromHopZuo {
    ///     color: Color::Huok2,
    ///     prof: Profession::Gua2,
    ///     dest: Coord(Row::IA, Column::L)
    /// }.serialize(), "黒弓LIA");
    ///
    /// assert_eq!(PureMove::NonTamMoveSrcDst {
    ///     src: Coord(Row::A, Column::Z),
    ///     dest: Coord(Row::E, Column::N),
    ///     is_water_entry_ciurl: true
    /// }.serialize(), "ZA片NE水");
    ///
    /// assert_eq!(PureMove::NonTamMoveSrcStepDstFinite {
    ///     src: Coord(Row::A, Column::Z),
    ///     step: Coord(Row::E, Column::T),
    ///     dest: Coord(Row::E, Column::N),
    ///     is_water_entry_ciurl: false
    /// }.serialize(), "ZA片TENE");
    ///
    /// // Note that [] denotes the first destination.
    /// // Since the first destination is neither the stepping square nor the final square,
    /// // it is not to be written in the standard notation.
    /// // Hence this additional information is denoted by [].
    /// assert_eq!(PureMove::TamMoveStepsDuringFormer {
    ///     src: Coord(Row::E, Column::K),
    ///     step: Coord(Row::I, Column::L),
    ///     first_dest: Coord(Row::I, Column::K),
    ///     second_dest: Coord(Row::E, Column::L)
    /// }.serialize(), "KE皇LI[KI]LE");
    ///
    /// assert_eq!(PureMove::TamMoveNoStep {
    ///     src: Coord(Row::E, Column::K),
    ///     first_dest: Coord(Row::I, Column::K),
    ///     second_dest: Coord(Row::E, Column::K)
    /// }.serialize(), "KE皇[KI]KE");
    ///
    /// assert_eq!(PureMove::TamMoveStepsDuringLatter {
    ///     src: Coord(Row::E, Column::K),
    ///     first_dest: Coord(Row::I, Column::K),
    ///     step: Coord(Row::I, Column::L),
    ///     second_dest: Coord(Row::E, Column::L)
    /// }.serialize(), "KE皇[KI]LILE");
    /// ```
    #[must_use]
    pub fn serialize(self) -> String {
        match self {
            PureMove::InfAfterStep {
                src,
                step,
                planned_direction,
            } => format!(
                "{}片{}心{}",
                serialize_coord(src),
                serialize_coord(step),
                serialize_coord(planned_direction)
            ),
            PureMove::NonTamMoveFromHopZuo { color, prof, dest } => format!(
                "{}{}{}",
                crate::serialize_color(color),
                crate::serialize_prof(prof),
                serialize_coord(dest)
            ),
            PureMove::NonTamMoveSrcDst {
                src,
                dest,
                is_water_entry_ciurl,
            } => format!(
                "{}片{}{}",
                serialize_coord(src),
                serialize_coord(dest),
                if is_water_entry_ciurl { "水" } else { "" }
            ),
            PureMove::NonTamMoveSrcStepDstFinite {
                src,
                dest,
                is_water_entry_ciurl,
                step,
            } => format!(
                "{}片{}{}{}",
                serialize_coord(src),
                serialize_coord(step),
                serialize_coord(dest),
                if is_water_entry_ciurl { "水" } else { "" }
            ),
            PureMove::TamMoveNoStep {
                src,
                first_dest,
                second_dest,
            } => format!(
                "{}皇[{}]{}",
                serialize_coord(src),
                serialize_coord(first_dest),
                serialize_coord(second_dest)
            ),
            PureMove::TamMoveStepsDuringFormer {
                src,
                first_dest,
                second_dest,
                step,
            } => format!(
                "{}皇{}[{}]{}",
                serialize_coord(src),
                serialize_coord(step),
                serialize_coord(first_dest),
                serialize_coord(second_dest)
            ),
            PureMove::TamMoveStepsDuringLatter {
                src,
                first_dest,
                second_dest,
                step,
            } => format!(
                "{}皇[{}]{}{}",
                serialize_coord(src),
                serialize_coord(first_dest),
                serialize_coord(step),
                serialize_coord(second_dest)
            ),
        }
    }
}

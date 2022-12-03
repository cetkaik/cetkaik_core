use super::{Color, Profession};

/// Describes which player it is
/// ／どちら側のプレイヤーであるかを指定する。
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Side {
    /// The player whose pieces point upward in your perspective, i.e. yours.
    /// ／君の視点で駒が上を向いている駒、つまり、君の駒。
    Upward,

    /// The player whose pieces point downward in your perspective, i.e. the opponent's.
    /// ／君の視点で駒が下を向いている駒、つまり、相手の駒。
    Downward,
}

impl std::ops::Not for Side {
    type Output = Side;

    fn not(self) -> Self::Output {
        match self {
            Side::Upward => Side::Downward,
            Side::Downward => Side::Upward,
        }
    }
}

/// Describes a piece that is not a Tam2 and points downward (i.e. opponents).
/// ／駒のうち、皇ではなくて、下向き（つまり相手陣営）のものを表す。
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct NonTam2PieceDownward {
    /// color of the piece／駒の色
    pub color: Color,
    /// profession of the piece／駒の職種
    pub prof: Profession,
}

/// Describes a piece that is not a Tam2 and points upward (i.e. yours).
/// ／駒のうち、皇ではなくて、上向き（つまり自分陣営）のものを表す。
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct NonTam2PieceUpward {
    /// color of the piece／駒の色
    pub color: Color,
    /// profession of the piece／駒の職種
    pub prof: Profession,
}

impl From<NonTam2PieceUpward> for Piece {
    fn from(from: NonTam2PieceUpward) -> Piece {
        Piece::NonTam2Piece {
            color: from.color,
            prof: from.prof,
            side: Side::Upward,
        }
    }
}

impl From<NonTam2PieceDownward> for Piece {
    fn from(from: NonTam2PieceDownward) -> Piece {
        Piece::NonTam2Piece {
            color: from.color,
            prof: from.prof,
            side: Side::Downward,
        }
    }
}

/// Describes a piece on the board.
/// ／盤上に存在できる駒を表現する。
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
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

#[must_use]
fn rotate_piece_or_null(p: Option<Piece>) -> Option<Piece> {
    let p = p?;
    match p {
        Piece::Tam2 => Some(p),
        Piece::NonTam2Piece { prof, color, side } => Some(Piece::NonTam2Piece {
            prof,
            color,
            side: !side,
        }),
    }
}

/// Denotes the position of a square by [row, col].
/// ／マス目の相対座標を [row, col] で表す。
///
pub type Coord = [usize; 2];

/// Serializes [`Coord`](./type.Coord.html) in JSON-style.
/// ／[`Coord`](./type.Coord.html) を JSON スタイルで文字列にする。
/// # Examples
/// ```
/// use cetkaik_core::*;
/// use cetkaik_core::relative::*;
///
/// assert_eq!(serialize_coord([5,6]), "[5,6]")
/// ```
#[must_use]
pub fn serialize_coord(coord: Coord) -> String {
    format!("[{},{}]", coord[0], coord[1])
}

/// Rotates the coordinate with the center of the board as the center of rotation.
/// ／盤の中心を基準に、座標を180度回転させる。
#[must_use]
pub const fn rotate_coord(c: Coord) -> Coord {
    [(8 - c[0]), (8 - c[1])]
}

/// Checks if the square is a tam2 nua2 (tam2's water), entry to which is restricted.
/// ／マスが皇水（たむぬあ）であるかどうかの判定
#[must_use]
#[allow(clippy::nonminimal_bool)]
pub const fn is_water([row, col]: Coord) -> bool {
    (row == 4 && col == 2)
        || (row == 4 && col == 3)
        || (row == 4 && col == 4)
        || (row == 4 && col == 5)
        || (row == 4 && col == 6)
        || (row == 2 && col == 4)
        || (row == 3 && col == 4)
        || (row == 5 && col == 4)
        || (row == 6 && col == 4)
}

const fn serialize_side(side: Side) -> &'static str {
    match side {
        Side::Upward => "↑",
        Side::Downward => "↓",
    }
}

/// Serializes [`Piece`](./enum.Piece.html).
/// ／[`Piece`](./enum.Piece.html) を文字列にする。
/// # Examples
/// ```
/// use cetkaik_core::*;
/// use cetkaik_core::relative::*;
///
/// assert_eq!(serialize_piece(Piece::Tam2), "皇");
/// assert_eq!(serialize_piece(Piece::NonTam2Piece {
///     prof: Profession::Uai1,
///     color: Color::Kok1,
///     side: Side::Downward
/// }), "赤将↓");
/// ```
#[must_use]
pub fn serialize_piece(p: Piece) -> String {
    match p {
        Piece::Tam2 => "皇".to_string(),
        Piece::NonTam2Piece { prof, color, side } => format!(
            "{}{}{}",
            super::serialize_color(color),
            super::serialize_prof(prof),
            serialize_side(side)
        ),
    }
}

/// Describes the board, the 9x9 squares, in terms of relative coordinates.
/// ／盤、つまり、9x9のマス目を、相対座標で表す。
pub type Board = [SingleRow; 9];

/// Describes a single row made up of 9 squares.
/// ／横一列の9マス、を表す。
pub type SingleRow = [Option<Piece>; 9];

/// Describes the field, which is defined as a board plus each side's hop1zuo1.
/// ／フィールドを表す。フィールドとは、盤に両者の手駒を加えたものである。
#[derive(Debug, Clone, Hash)]
pub struct Field {
    /// board／盤
    pub current_board: Board,

    /// hop1zuo1 for the Upward (i.e. you)／Upward側（あなた）の手駒
    pub hop1zuo1of_upward: Vec<NonTam2PieceUpward>,

    /// hop1zuo1 for the Downward (i.e. opponent)／Downward側（相手）の手駒
    pub hop1zuo1of_downward: Vec<NonTam2PieceDownward>,
}

/// Returns the initial configuration as specified in the y1 huap1 (the standardized rule).
/// The red king points upward (i.e. you)
/// ／官定で定められた初期配置を与える。赤王が自分側にある。
#[must_use]
pub fn yhuap_initial_board_where_red_king_points_upward() -> Board {
    rotate_board(yhuap_initial_board_where_black_king_points_upward())
}

/// Returns the initial configuration as specified in the y1 huap1 (the standardized rule).
/// The black king points upward (i.e. you)
/// ／官定で定められた初期配置を与える。黒王が自分側にある。
#[must_use]
#[allow(clippy::too_many_lines)]
pub const fn yhuap_initial_board_where_black_king_points_upward() -> Board {
    [
        [
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kua2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Maun1,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kaun1,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Uai1,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Io,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Uai1,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kaun1,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Maun1,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kua2,
                side: Side::Downward,
            }),
        ],
        [
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Tuk2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Gua2,
                side: Side::Downward,
            }),
            None,
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Dau2,
                side: Side::Downward,
            }),
            None,
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Dau2,
                side: Side::Downward,
            }),
            None,
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Gua2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Tuk2,
                side: Side::Downward,
            }),
        ],
        [
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Nuak1,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
                side: Side::Downward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
                side: Side::Downward,
            }),
        ],
        [None, None, None, None, None, None, None, None, None],
        [
            None,
            None,
            None,
            None,
            Some(Piece::Tam2),
            None,
            None,
            None,
            None,
        ],
        [None, None, None, None, None, None, None, None, None],
        [
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Nuak1,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kauk2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kauk2,
                side: Side::Upward,
            }),
        ],
        [
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Tuk2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Gua2,
                side: Side::Upward,
            }),
            None,
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Dau2,
                side: Side::Upward,
            }),
            None,
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Dau2,
                side: Side::Upward,
            }),
            None,
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Gua2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Tuk2,
                side: Side::Upward,
            }),
        ],
        [
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kua2,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Maun1,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Kaun1,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Kok1,
                prof: Profession::Uai1,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Io,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Uai1,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kaun1,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Maun1,
                side: Side::Upward,
            }),
            Some(Piece::NonTam2Piece {
                color: Color::Huok2,
                prof: Profession::Kua2,
                side: Side::Upward,
            }),
        ],
    ]
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
            Side::Upward => self
                .hop1zuo1of_upward
                .push(NonTam2PieceUpward { color, prof }),
            Side::Downward => self
                .hop1zuo1of_downward
                .push(NonTam2PieceDownward { color, prof }),
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
            Side::Upward => {
                let mut that = self.clone();
                let index = that
                    .hop1zuo1of_upward
                    .iter()
                    .position(|x| *x == NonTam2PieceUpward { color, prof })?;
                that.hop1zuo1of_upward.remove(index);
                Some(that)
            }
            Side::Downward => {
                let mut that = self.clone();
                let index = that
                    .hop1zuo1of_downward
                    .iter()
                    .position(|x| *x == NonTam2PieceDownward { color, prof })?;
                that.hop1zuo1of_downward.remove(index);
                Some(that)
            }
        }
    }
}

/// Rotates a board.
/// ／盤を180度回転させ、自分陣営と相手陣営を入れ替える。
#[must_use]
pub fn rotate_board(b: Board) -> Board {
    let mut ans: Board = [
        [None, None, None, None, None, None, None, None, None],
        [None, None, None, None, None, None, None, None, None],
        [None, None, None, None, None, None, None, None, None],
        [None, None, None, None, None, None, None, None, None],
        [None, None, None, None, None, None, None, None, None],
        [None, None, None, None, None, None, None, None, None],
        [None, None, None, None, None, None, None, None, None],
        [None, None, None, None, None, None, None, None, None],
        [None, None, None, None, None, None, None, None, None],
    ];
    for i in 0..9 {
        for j in 0..9 {
            ans[i][j] = rotate_piece_or_null(b[8 - i][8 - j]);
        }
    }
    ans
}

/// Calculates the distance between two points.
/// The distance is defined as the larger of the difference between either the x or y coordinates.
/// ／2点間の距離（x座標の差およびy座標の差のうち小さくない方）を計算する。
/// # Examples
/// ```
/// use cetkaik_core::relative::*;
/// assert_eq!(5, distance([4,5], [4,0]));
/// assert_eq!(3, distance([4,5], [1,2]));
/// assert_eq!(3, distance([1,2], [4,5]));
/// ```
///
/// # Panics
/// Panics if the `Coord` is so invalid that it does not fit in `i32`.
/// ／`Coord` に入っている座標が `i32` に収まらないほど巨大であれば panic する。
#[must_use]
pub fn distance(a: Coord, b: Coord) -> i32 {
    let [x1, y1] = a;
    let [x2, y2] = b;

    let x_distance = (i32::try_from(x1).unwrap() - i32::try_from(x2).unwrap()).abs();
    let y_distance = (i32::try_from(y1).unwrap() - i32::try_from(y2).unwrap()).abs();

    x_distance.max(y_distance)
}

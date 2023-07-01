import javax.swing.event.HyperlinkListener

object TikTacToe {
  // numbers
  trait Nat
  class _0 extends Nat
  class Succ[N <: Nat] extends Nat
  type _1 = Succ[_0]
  type _2 = Succ[_1]
  type _3 = Succ[_2]
  type _4 = Succ[_3]
  type _5 = Succ[_4]

  // player
  type Player = "X" | "O"
  type Cell = Player | "_"

  //type level list
  trait Hlist

  class HNil extends Hlist //empty

  infix class ::[H, T <: Hlist] extends Hlist

  // board
  type Board = Hlist
  type EmptyRow = "_" :: "_" :: "_" :: HNil
  type EmptyBoard = EmptyRow :: EmptyRow :: EmptyRow :: HNil



  //predicates
  trait Length[L <: Hlist, N <: Nat] // length[L, N] exist if length L is N
  given zeroLength: Length[HNil, _0] with {} // axiom
  given lengthInductive[H, T <: Hlist, N <: Nat](using Length[T, N]): Length[H::T, Succ[N]] with {}



  // winner
  // by row
  trait SameValues[L <: Hlist, V]
  given svBasic[V]: SameValues[HNil, V] with {}
  given svInductive[T <: Hlist, V] (using SameValues[T, V]): SameValues[V :: T, V] with {}

  trait WinsByRow[B <: Board, W <: Player]
  given winsFirstRow[R <: Hlist, RT <: Hlist, P <: Player] (using SameValues[R, P]): WinsByRow[R :: RT, P] with {}
  given winsAnyRow[R <: Hlist, RT <: Hlist, P <: Player] (using WinsByRow[RT, P]): WinsByRow[R :: RT, P] with {}


  // by columns
  // take nth element
  trait TakeNth[L <: Hlist, N <: Nat, V]
  given tnBasic[T <: Hlist, V]: TakeNth[V :: T, _0, V] with {}
  given tnInductive[H, T <: Hlist, N <: Nat, V](using TakeNth[T, N, V]): TakeNth[H :: T, Succ[N], V] with {}

  // map column
  trait MapColumn[B <: Board, C <: Nat, O <: Hlist]
  // matrix 1xn => 1 value
  given mpBasic[R <: Hlist, C <: Nat, V](using TakeNth[R,C,V]): MapColumn[R::HNil, C, V::HNil] with {}
  // matrix mxn => take 1st value out of the 1st row, mapColumn[(m-1)xn]
  given mpInductive[R <: Hlist, RT <: Hlist, C <: Nat, V, VT <: Hlist] (
    using TakeNth[R, C, V], MapColumn[RT,C,VT]
   ): MapColumn[R :: RT, C, V :: VT] with {}

  trait WinsByColumnUpTo[B <: Board, C <: Nat, W <: Player]
  given winsFirstColumn[B <: Board, L <: Hlist, W <: Player](
    using MapColumn[B,_0, L], SameValues[L,W]
  ): WinsByColumnUpTo[B, _1, W] with {}
  given winsAnyColumn[B <: Board, C <: Nat, L <: Hlist, W <: Player](
    using MapColumn[B,C,L], SameValues[L,W]
  ): WinsByColumnUpTo[B, Succ[C], W] with {}
  given winsAnyColumn2[B <: Board, C <: Nat, W <: Player] (
    using WinsByColumnUpTo[B,C,W]
  ): WinsByColumnUpTo[B, Succ[C], W] with {}

  trait WinsByColumn[B <: Board, W <: Player]
  given winsByAnyColumn[FR <: Hlist, RT <: Hlist, L <: Nat, W <: Player](
    using Length[FR, L], WinsByColumnUpTo[FR :: RT, L, W]
  ): WinsByColumn[FR :: RT, W] with {}


  // by diag1
  trait Diag1[B <: Board, I <: Nat, D <: Hlist]
  given diag1Basic[R <: Hlist, N <: Nat, V](
    using Length[R, Succ[N]], TakeNth[R, N, V]
  ): Diag1[R :: HNil, N, V :: HNil] with {}
  given diag1Inductive[R <: Hlist, RT <: Hlist, N <: Nat, V, VT <: Hlist](
    using Diag1[RT, Succ[N], VT], TakeNth[R, N, V]
  ): Diag1[R :: RT, N, V :: VT] with {}

  trait WinsByDiag1[B <: Board, W <: Player]
  given wbd1[B <: Board, D1 <: Hlist, W <: Player](
    using Diag1[B, _0, D1], SameValues[D1, W]
  ): WinsByDiag1[B, W] with {}


  // by diag2
  trait Diag2[B <: Board, I <: Nat, D <: Hlist]
  given diag2Basic[V, T <: Hlist]: Diag2[(V :: T) :: HNil, _0, V :: HNil] with {}
  given diag2Inductive[R <: Hlist, RT <: Hlist, I <: Nat, V, VT <: Hlist](
    using Diag2[RT , I, VT], TakeNth[R, Succ[I], V]
  ): Diag2[R :: RT, Succ[I], V :: VT] with {}

  trait WinsByDiag2[B <: Board, W <: Player]
  given wbd2[R <: Hlist, RT <: Hlist, N <: Nat, D2 <: Hlist, W <: Player](
    using Length[R, Succ[N]], Diag2[R :: RT, N, D2], SameValues[D2, W]
  ): WinsByDiag2[R :: RT, W] with {}


  // wins
  trait Wins[B <: Board, W <: Player]
  given row[B <: Board, W <: Player](using WinsByRow[B, W]): Wins[B, W] with {}
  given col[B <: Board, W <: Player](using WinsByColumn[B, W]): Wins[B, W] with {}
  given d1[B <: Board, W <: Player](using WinsByDiag1[B, W]): Wins[B, W] with {}
  given d2[B <: Board, W <: Player](using WinsByDiag2[B, W]): Wins[B, W] with {}


  def main(args: Array[String]): Unit = {
  val a = summon[Wins[
    ("_" :: "_" :: "O" :: HNil) ::
    ("X" :: "X" :: "X" :: HNil) ::
    ("O" :: "_" :: "_" :: HNil) ::
    HNil,
    "X"]]
  }

}

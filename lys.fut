import "lib/github.com/diku-dk/lys/lys"
import "lib/github.com/diku-dk/segmented/segmented"
import "lib/github.com/diku-dk/cpprandom/random"

module rng = xorshift128plus
module dist = uniform_int_distribution i64 u64 rng

type dir = #n | #w | #e | #s
type point = (i64, i64)
type line = (point, point)

def no_point : point = (-1, -1)

-- | Move along direction.
def move (d: dir) ((i, j): point) =
  match d
  case #n -> (i - 1, j)
  case #w -> (i, j - 1)
  case #e -> (i, j + 1)
  case #s -> (i + 1, j)

def point_lte (w: i64) ((ax, ay): point) ((bx, by): point) : bool =
  ax * w + ay <= bx * w + by

def get 'a ((i, j): point) (g: [][]a) =
  g[i, j]

def compare (v1: i64) (v2: i64) : i64 =
  if v2 > v1 then 1 else if v1 > v2 then -1 else 0

def slope ((x1, y1): point) ((x2, y2): point) : f64 =
  if x2 == x1
  then if y2 > y1 then 1 else -1
  else f64.i64 (y2 - y1) / f64.i64 (i64.abs (x2 - x1))

def put_on_grid [h] [w] [n] (grid: *[h][w]u32) (xys: [n](i64, i64)) : [h][w]u32 =
  let is = map (\(x, y) -> w * y + x) xys
  in unflatten (scatter (flatten grid) is (replicate n argb.white))

def mk_grid [n] (h: i64) (w: i64) (xys: [n](i64, i64)) : [][]u32 =
  put_on_grid (unflatten (replicate (h * w) argb.black)) xys

def points_in_line ((x1, y1), (x2, y2)) : i64 =
  1 + i64.max (i64.abs (x2 - x1)) (i64.abs (y2 - y1))

def get_point_in_line ((p1, p2): line) (i: i64) : point =
  if i64.abs (p1.0 - p2.0) > i64.abs (p1.1 - p2.1)
  then let dir = compare p1.0 p2.0
       let sl = slope p1 p2
       in ( p1.0 + dir * i
          , p1.1 + i64.f64 (f64.round (sl * f64.i64 i))
          )
  else let dir = compare (p1.1) (p2.1)
       let sl = slope (p1.1, p1.0) (p2.1, p2.0)
       in ( p1.0 + i64.f64 (f64.round (sl * f64.i64 i))
          , p1.1 + i * dir
          )

def drawlines [n] (h: i64) (w: i64) (lines: [n]line) : [h][w]u32 =
  let xys =
    expand points_in_line get_point_in_line lines
  in mk_grid h w xys

def drawlines' [n] (h: i64) (w: i64) (lines: [n]line) : [h][w]u32 =
  let xys =
    expand points_in_line get_point_in_line lines
  in mk_grid h w xys

def flat_point (w: i64) ((x, y): point) : i64 = x * w + y

def in_bounds [h] [w] 'a (_: [h][w]a) ((i, j): point) =
  i >= 0 && i < h && j >= 0 && j < w

type edge = (point, point)

-- | Normalise an edge such that it goes from the lesser index to the greater.
def norm_edge w ((a, b): edge) : edge =
  if point_lte w a b then (a, b) else (a, b)

-- | Create normalised edges linking all neighbouring pixels with the same
-- colour.
def mk_edges [h] [w] (img: [h][w]u32) : []edge =
  let mk_edge dir p =
    let p' = move dir p
    in if in_bounds img p' && get p img == get p' img
       then norm_edge w (p, p')
       else (no_point, no_point)
  let edges_raw =
    tabulate_2d h w \i j ->
      [mk_edge #n (i, j), mk_edge #s (i, j), mk_edge #w (i, j), mk_edge #e (i, j)]
  let valid_edge (a, b) = a != no_point && b != no_point
  in filter valid_edge (flatten_3d edges_raw)

def region_label_smarter [h] [w] (img: [h][w]u32) =
  let edges = map (\(a, b) -> (flat_point w a, flat_point w b)) (mk_edges img)
  let forest = flatten (tabulate_2d h w \i j -> flat_point w (i, j))
  let (forest', _) =
    loop (forest, edges) while length edges > 0 do
      -- Try to insert as many parents as we can.
      let forest' =
        reduce_by_index forest
                        i64.max
                        (-1)
                        -- Only insert new parents for roots.
                        (map (\(a, _) -> if forest[a] == a then a else -1) edges)
                        (map (.1) edges)
      -- Remove the edges we failed to insert.
      let edges' = filter (\(a, b) -> forest'[a] != b) edges
      -- Update the edges with the new roots.
      let edges'' = map (\(a, b) -> (forest'[a], forest'[b])) edges'
      -- Advance the forest a bit.
      let forest'' = map (\a -> forest'[a]) forest'
      in (forest'', edges'')
  -- TODO: this last step should be a proper ranking instead to get the right
  -- asymptotics.
  in unflatten (map (\a -> loop a while forest'[a] != a do forest'[a]) forest')

def colourise_regions [h] [w] (labels: [h][w]i64) : [h][w]u32 =
  let f l = u32.i64 l
  in map (map f) labels

type text_content = ()

module lys : lys with text_content = text_content = {
  type~ state =
    { time: f32
    , h: i64
    , w: i64
    , lines: []line
    , rng: rng.rng
    }

  def grab_mouse = false

  def maybe_add_line (s: state) =
    if s.time > 1
    then let (rng, x1) = dist.rand (0, s.w) s.rng
         let (rng, x2) = dist.rand (0, s.w) rng
         let (rng, y1) = dist.rand (0, s.h) rng
         let (rng, y2) = dist.rand (0, s.h) rng
         in s with rng = rng
              with lines = [((x1, y1), (x2, y2))] ++ s.lines
              with time = 0
    else s

  def init (seed: u32) (h: i64) (w: i64) : state =
    { time = 0
    , w
    , h
    , rng = rng.rng_from_seed [i32.u32 seed]
    , lines =
        [ ((10, 10), (100, 100))
        , ((100, 10), (10, 100))
        , ((15, 15), (150, 90))
        ]
    }

  def resize (h: i64) (w: i64) (s: state) =
    s with h = h with w = w

  def keydown (_key: i32) (s: state) =
    s

  def keyup (_key: i32) (s: state) =
    s

  def event (e: event) (s: state) =
    match e
    case #step td ->
      maybe_add_line (s with time = s.time + td)
    case _ -> s

  def render (s: state) =
    let xys =
      expand points_in_line get_point_in_line s.lines
    let grid = unflatten (replicate (s.h * s.w) argb.black)
    let grid = put_on_grid grid xys
    let grid = colourise_regions (region_label_smarter grid)
    in put_on_grid grid xys

  type text_content = text_content

  def text_format () =
    ""

  def text_content (_render_duration: f32) (_s: state) : text_content =
    ()

  def text_colour = const argb.yellow
}

import Std.Data.HashMap
/-!
# Word-level tokenizer

TinyStories is written with a deliberately small vocabulary, which is what makes
word-level modelling viable here: measured on the corpus slice, 2048 lowercased
types cover 96.6% of all token occurrences (8192 would reach 100%, but every
extra row costs both parameters and output-projection FLOPs).

Choosing words over characters matters for a model this small. A character model
must spend capacity learning to spell before it can learn to say anything, and
at a few hundred thousand parameters there is not enough left over.

Text is lowercased before tokenizing. That trades away proper nouns'
capitalisation -- restored heuristically in `detokenize` -- for a smaller
vocabulary and better coverage.
-/
namespace TinyLM

/-- Reserved ids. Real words start at `firstWord`. -/
def unkId : Nat := 0
def bosId : Nat := 1
def eosId : Nat := 2
def firstWord : Nat := 3

def specialTokens : Array String := #["<unk>", "<bos>", "<eos>"]

structure Vocab where
  /-- id -> surface form -/
  toStr : Array String
  /-- surface form -> id -/
  toId : Std.HashMap String Nat
  deriving Inhabited

namespace Vocab

def size (v : Vocab) : Nat := v.toStr.size

def encodeWord (v : Vocab) (w : String) : Nat :=
  v.toId.getD w unkId

def decodeId (v : Vocab) (i : Nat) : String :=
  v.toStr[i]!

def ofArray (words : Array String) : Vocab :=
  let toStr := specialTokens ++ words
  { toStr, toId := toStr.zipIdx.foldl (fun m (w, i) => m.insert w i) ∅ }

end Vocab

/-! ## Scanning

A hand-rolled scanner rather than a regex, since Lean core has no regex engine
and the token classes here are trivial: runs of letters (with an internal
apostrophe, so `don't` stays one token) and single punctuation marks.
Everything else -- digits, stray symbols, whitespace -- acts as a separator. -/

private def isWordChar (c : Char) : Bool :=
  c.isAlpha || c == '\''

private def isPunct (c : Char) : Bool :=
  c == '.' || c == ',' || c == '!' || c == '?' || c == ';' || c == ':' || c == '"'

/-- Split raw text into lowercase word and punctuation tokens. -/
partial def tokenizeText (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  let mut out : Array String := #[]
  let mut i := 0
  while i < n do
    let c := cs[i]!
    if isWordChar c then
      let start := i
      let mut j := i
      while j < n && isWordChar cs[j]! do
        j := j + 1
      -- A leading/trailing apostrophe is punctuation-ish noise, so trim it.
      -- Done on `List Char`: `String.dropWhile` yields a `String.Slice` here.
      let chars := (Array.extract cs start j).toList.map Char.toLower
      let chars := (chars.dropWhile (· == '\'')).reverse.dropWhile (· == '\'')
      if !chars.isEmpty then
        out := out.push (String.ofList chars.reverse)
      i := j
    else if isPunct c then
      out := out.push (String.singleton c)
      i := i + 1
    else
      i := i + 1
  return out

/-- Encode text to ids, without adding `<bos>`/`<eos>`. -/
def encode (v : Vocab) (s : String) : Array Nat :=
  (tokenizeText s).map v.encodeWord

/-! ## Detokenizing

Sampled ids come back as a flat word sequence; this puts the surface
conventions back: no space before punctuation, capitals after sentence-final
punctuation, and a capital `I`. It is cosmetic -- the model is never scored on
it -- but it is the difference between output that reads as prose and output
that reads as a token dump. -/

private def endsSentence (s : String) : Bool :=
  s == "." || s == "!" || s == "?"

private def capitalize (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: rest => String.singleton c.toUpper ++ String.ofList rest

def detokenize (toks : Array String) : String := Id.run do
  let mut out := ""
  let mut capNext := true
  for t in toks do
    if specialTokens.contains t then
      continue
    let isP := match t.toList with
               | [c] => isPunct c
               | _   => false
    let piece := if capNext && !isP then capitalize t else if t == "i" then "I" else t
    if out.isEmpty || isP then
      out := out ++ piece
    else
      out := out ++ " " ++ piece
    capNext := endsSentence t
  return out

def decode (v : Vocab) (ids : Array Nat) : String :=
  detokenize (ids.map v.decodeId)

/-! ## Building a vocabulary

Counts every type in the corpus, keeps the `n` most frequent. Ties are broken by
the word itself so the vocabulary is a deterministic function of the corpus --
the checkpoint format stores ids, not strings, so a reshuffled vocabulary would
silently invalidate every saved model. -/

def buildVocab (corpus : Array String) (n : Nat) : Vocab := Id.run do
  let mut counts : Std.HashMap String Nat := ∅
  for doc in corpus do
    for w in tokenizeText doc do
      counts := counts.insert w (counts.getD w 0 + 1)
  let mut arr := counts.toArray
  -- most frequent first; alphabetical within a count
  let sorted := arr.qsort (fun (w1, c1) (w2, c2) =>
    if c1 == c2 then w1 < w2 else c1 > c2)
  let keep := sorted.extract 0 (min n sorted.size)
  return Vocab.ofArray (keep.map Prod.fst)

/-! ## Persistence

One token per line, ids implied by line order. Special tokens are written out
too so the file is a complete description of the mapping. -/

def Vocab.toFileContents (v : Vocab) : String :=
  String.intercalate "\n" v.toStr.toList

def Vocab.ofFileContents (s : String) : Vocab :=
  let lines := (s.splitOn "\n").filter (fun l => !l.isEmpty)
  let arr := lines.toArray
  { toStr := arr, toId := arr.zipIdx.foldl (fun m (w, i) => m.insert w i) ∅ }

end TinyLM

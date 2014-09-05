% Real World Agda
% notogawa
% 2014/9/6

# 定理証明系の"実用"

* for 証明士
    * 何らかの命題が証明できる
    * ある意味動くものができる必要は無い
* for プログラマ
    * 処理(関数)が定義できる
    * 定義した処理について何らかの性質が証明できる
    * 証明済みの処理が**そのまま動かせる**

# 動かせるものを得る方法

* Coq
    * 各言語へのExtract
* Agda
    * Haskell backend
        * **MAlonzo**
    * Epic backebnd
    * JavaScript backend

# 本日のお題

標準入出力の各行を順次反転して印字

* 以下のHaskellと同じ挙動

~~~~
main = interact $ unlines . map reverse . lines
~~~~

~~~~
$ ./src/Main
1234           <- 入力してEnter
4321           <- 出力される
abracadabra    <- 入力してEnter
arbadacarba    <- 出力される
[Ctrl+D]       <- 終了
~~~~

ただし，`reverse`について以下を証明しておく

~~~~
reverse . reverse = id
~~~~

# reverse の定義

~~~~
rev : ∀ {a} {A : Set a} → List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ [ x ]
~~~~

末尾再帰がどうこうとか細かいことはおいといて．

# reverse . reverse = id の証明

~~~~
lemma : ∀ {a} {A : Set a} (x : A) (xs : List A) → rev (xs ∷ʳ x) ≡ x ∷ rev xs
lemma x [] = refl
lemma x (_ ∷ xs)
  rewrite lemma x xs
        = refl

revrev-is-id : ∀ {a} {A : Set a} (xs : List A) → rev (rev xs) ≡ xs
revrev-is-id [] = refl
revrev-is-id (x ∷ xs)
  rewrite lemma x (rev xs)
        | revrev-is-id xs
        = refl
~~~~

# Agda(MAlonzo)での関数の動かし方

いずれも一度Haskellになる

* Agdaで全て書く
    * 実行バイナリを得る
    * main関数他もAgda内で
* Agdaの関数をHaskellから使う (2.3.4 以降)
    * Haskellのモジュールを得る
    * 証明された一部の関数だけを得る
    * main関数他はHaskellで

# Agdaで全て書く編

# とりあえずHello,World!

~~~~
module HelloWorld where

open import IO

main = run (putStrLn "Hello,World!")
~~~~

# コンパイル

~~~~
$ agda -c -i. -i/usr/share/agda-stdlib HelloWorld.agda
    Skipping Level (/usr/share/agda-stdlib/Level.agdai).
   Skipping Function (/usr/share/agda-stdlib/Function.agdai).
(snip.)
Skipping HelloWorld (/home/notogawa/work/proofsummit2014/HelloWorld.agdai).
Compiling Agda.Primitive in /usr/share/agda-2.4.0.2/ghc-7.8.3/lib/prim/Agda/Primitive.agdai to /home/notogawa/work/proofsummit2014/MAlonzo/Code/Agda/Primitive.hs
Compiling Algebra in /usr/share/agda-stdlib/Algebra.agdai to /home/notogawa/work/proofsummit2014/MAlonzo/Code/Algebra.hs
(snip.)
Compiling Relation.Unary in /usr/share/agda-stdlib/Relation/Unary.agdai to /home/notogawa/work/proofsummit2014/MAlonzo/Code/Relation/Unary.hs
Calling: ghc -O -o /home/notogawa/work/proofsummit2014/HelloWorld -Werror -i/home/notogawa/work/proofsummit2014 -main-is MAlonzo.Code.HelloWorld /home/notogawa/work/proofsummit2014/MAlonzo/Code/HelloWorld.hs --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns
[ 1 of 95] Compiling MAlonzo.RTE      ( MAlonzo/RTE.hs, MAlonzo/RTE.o )
[ 2 of 95] Compiling MAlonzo.Code.Agda.Primitive ( MAlonzo/Code/Agda/Primitive.hs, MAlonzo/Code/Agda/Primitive.o )
(snip.)
[95 of 95] Compiling MAlonzo.Code.HelloWorld ( /home/notogawa/work/proofsummit2014/MAlonzo/Code/HelloWorld.hs, /home/notogawa/work/proofsummit2014/MAlonzo/Code/HelloWorld.o )
agda -c -i. -i/usr/share/agda-stdlib HelloWorld.agda  83.29s user 12.98s system 97% cpu 1:38.86 total
~~~~

# コンパイル結果

* 気になるところ
    * 1分半以上かかってる
    * Haskellのモジュールが95個作られてる
* まぁ，安い安い．キニシナイ！

* 実行

~~~~
$ ./HelloWorld
Hello,World!
~~~~

# では，お題に挑戦

* IO
    * 無限の入力とCostring
* parse
    * Partiality Monad

# 無限の入力

* 標準入力をはじめ，多くの入力の特徴
    * 終わりがいつかわからない
        * ソケット通信
        * /dev/random
    * 所謂，ストリーム

* Agdaの標準入力の型

~~~~
getContents : IO Costring
~~~~

# Costring

* 文字の余リスト

~~~~
Costring : Set
Costring = Colist Char
~~~~

* (対して)Stringは何か特殊な型
    * 文字のリストと相互変換可能
    * HaskellではStringにマップされる

# 余リスト

* 終わらないかもしれないリスト構造
    * 一段階分解してはじめて続くか終わるかがわかる
    * Coinductive Data Type

~~~~
data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A
~~~~

* (対して)Listは必ず終わりがあるリスト構造
    * 一段階ずつ`_∷_`して作られていることがわかっている
    * Inductive Data Type

~~~~
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
~~~~

# 無限の記号？ - Agda の Coinduction

~~~~
∞  : ∀ {a} (A : Set a) → Set a
♯_ : ∀ {a} {A : Set a} → A → ∞ A
♭  : ∀ {a} {A : Set a} → ∞ A → A
~~~~

* `∞`は delay operator
    * 中身が謎のヴェールに"包まれた"型かどうか
    * 評価が遅延するという意味を持つ型を作る
* `♯`は delay function
    * 謎のヴェールで"包む"
    * 評価を遅延させることを示す
* `♭`は force function
    * 謎のヴェールを"剥す"
    * 遅延させられた値の評価を進める

# つまり，どういうことだってばよ？

~~~~
data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A
~~~~

* Colistの値からパターンマッチで先頭`x`と残り`xs`が取り出せる
    * かもしれないし，もちろん`[]`かもしれない
* ただし，`xs`は`♭`してあげないとどうなっているかわからない
    * `xs`から次のパターンマッチはできない
    * `♭ xs`から次のパターンマッチができる

# Costringを各行毎に分割しよう

* 次のような型の関数を作りたい
    * 先頭行のString
    * それ以降の行のCostring

~~~~
takeLine : Costring → String × Costring
~~~~

~~~~
takeLine "foo\nbar\n\baz" => "foo" , "bar\nbaz"
~~~~

* `×`はタプルで，`,`はそのコンストラクタ
    * 少し違うけど，そうだと思って

# さあ，作ろう

作れません

# なぜ作れないか

~~~~
takeLine : Costring → String × Costring
~~~~

* 停止性が示せない

* 終わらないかもしれないデータから何か(改行コード)を探す
    * 一切改行がないままCostringが無限に続くケースで停止しない

~~~~
takeCount : ℕ → Costring → String × Costring
~~~~

* (比較)こちらは停止性が示せる
    * 延々続いても規定個取るだけ

# これでFinish！？な訳無いデショ！

2つの状況を示すCoinductive Data Typeを作る

* "まだ"目的の値が作れるときではない
    * (Costringの)分解を続ける
* "今"まさに目的の値を得た
    * この瞬間を待っていたんだ！

~~~~
data _⊥ {a} (A : Set a) : Set a where
  now   : (x : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥
~~~~

`takeLine`の型を次のように変更

~~~~
takeLine : Costring → (String × Costring) ⊥
~~~~

# takeLineを定義する

~~~~
takeLine : Costring → (String × Costring) ⊥
takeLine xs = go "" xs where
  go : String → Costring → (String × Costring) ⊥
  go acc [] = now (acc , []) -- 終端きた
  go acc (x ∷ xs) with fromList [ x ]
  go acc (x ∷ xs) | "\n" = now (acc , (♭ xs)) -- 改行きた
  go acc (x ∷ xs) | last = later (♯ go (acc ++ last) (♭ xs))
~~~~

* 改行が来ないうちは，`later`が重なる
    * Coinductiveな場合，再帰で**構造が大きくならなければならない**
* 最後はnowになる
    * Coinductiveなので**なるかもしれない**

# laterを剥す

* `A ⊥`の値から単純に`now`を探して`A`の値取り出すことはできない
    * 停止性
* `later`を(支障無く)剥せるタイミングは`IO`でのみ
* `IO`にだけはinfinity large computationの構成を許す版がある
    * `IO.Primitive`(許さない版)
    * `IO`(許す版)．`IO.Primitive`のラッパ．`run`を使う

~~~~
eachline : (String → String) → Costring → IO ⊤
eachline f = go ∘ takeLine where
  go : (String × Costring) ⊥ → IO ⊤
  go (now (line , xs)) = ♯ putStrLn (f line) >> ♯ go (takeLine xs)
  go (later x) = ♯ return tt >> ♯ go (♭ x)
~~~~

* 無意味な`later`を**何もしない操作**で消費
    * return tt のこと

# とりあえずの解答

~~~~
main = run (♯ getContents >>= ♯_ ∘ eachline ( fromList ∘ rev ∘ toList) )
~~~~

* まだ問題がある
    * 入力が終わらないと出力されない
        * HaskellのunsafeInterleaveIO的挙動になっていない
    * 終わりが来ても空行が出力され続ける
        * `takeLine`が終端を認識できる型になっていない

* 完全版は
    * https://github.com/notogawa/agda-haskell-example
    * src/Main.hs

# Partiality Monad

* Partiality Monad
    * `now`と`later`による構造`_⊥`はモナド
    * Agda標準ライブラリにも入っている

# Agdaで全て書く編…結果

* できなくはない
* が，とてもつらい
    * Coinductivity
    * Termination Checker
    * Partiality Monad
    * Long Compile Time
* 初心者にオススメするのは少し難しいかもしれない
* いたるところPartiality Monadによるストリーミング処理
    * conduit/pipes for Agda が要る？

# Agdaの関数をHaskellから使う編

# Haskellのコード生成に使うFFIプラグマ

Agdaから生成されるHaskellモジュールに対して

* `IMPORT`
    * 指定Haskellモジュールを生成モジュール内でimportする
* `COMPILED`
    * あるAgdaの関数を指定のHaskellコードに対応させる
* `COMPILED_TYPE`
    * あるAgdaの型を指定のHaskell型に対応させる
* `COMPILED_DATA`
    * あるAgdaの代数的データ型を指定のHaskellの代数的データ型に対応させる
    * そのコンストラクタも指定のコンストラクタに対応させる

# そして今回のメイン

* `COMPILED_EXPORT`
    * あるAgadの関数を指定の名前のHaskell関数として生成する
    * 何も指定しなければ機械生成な名前
        * `d123`のような

~~~~
-- reverse
rev : ∀ {a} {A : Set a} → List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ [ x ]

rev' = rev -- 理由は後述

{-# COMPILED_EXPORT rev' rev' #-}
~~~~

# Haskellモジュールの生成

コンパイルはするが`main`は無いので

~~~~
agda -c --no-main -i/usr/share/agda-stdlib -isrc src/Example.agda
~~~~

* AgdaのモジュールXから
    * 例: Example.agda
* HaskellのモジュールMAlonzo.Code.Xが
    * 例: MAlonzo/Code/Example.hs

# 生成される関数

~~~~
rev : ∀ {a} {A : Set a} → List A → List A
~~~~

~~~~
*MAlonzo.Code.Example> :t rev'
rev' :: () -> () -> Data.FFI.AgdaList xa xA -> Data.FFI.AgdaList xa xA
~~~~

* `Data.FFI.AgdaList xa xA` はリスト `[xA]`
* implicit parameter も explicit parameter に
* 型のレベルが`()`に
* 型も`()`に

# 生成された関数を使い易くするためのラッパ

`()`や`AgdaList`が自明かつ邪魔なので

~~~~
module Example (rev) where

import MAlonzo.Code.Example

rev :: [a] -> [a]
rev = rev' () ()
~~~~

この`Example`モジュールをimportして`rev`関数を使うようにする

# Agdaを伴うHaskellプロジェクトのCabalize

* ディレクトリ構造

~~~~
./Setup.hs
./agda-haskell-example.cabal
./src/Example.agda
./src/Example.hs
./src/Main.hs
~~~~

* Setup.hsカスタマイズ

~~~~
main = defaultMainWithHooks hook where
    customPreBuild args flags = do
      system "agda -c --no-main -i/usr/share/agda-stdlib -isrc src/Example.agda"
      preBuild simpleUserHooks args flags
    hook = simpleUserHooks { preBuild = customPreBuild }
~~~~

# 落とし穴集

* COMPILED_EXPORTバグ
* 証明項の扱い
* Inductive/Coinductive Data Type の区別
* ghc-mod/emacsが激重

# COMPILED_EXPORTバグ

revを直接COMPILED_EXPORTしなかった理由

~~~~
rev' = rev
{-# COMPILED_EXPORT rev' rev' #-}
~~~~

* `rev`を直接exportするとコンパイルできないコードが生成される
    * https://code.google.com/p/agda/issues/detail?id=1252
    * 2.4.0.2まで存在
    * 2.4.2以降fixed (されてるハズ)
* 2.4.2以降を使うか`rev'`のようにワンクッションで回避

# 証明項の扱い

証明項を引数に持つ関数のexport

~~~~
head : ∀ {a} {A : Set a} (xs : List A) → {xs≢[] : xs ≢ []} → A
head [] {xs≠[]} = ⊥-elim (xs≠[] refl)
head (x ∷ xs) = x
{-# COMPILED_EXPORT head safeHead' #-}
~~~~

`_≡_`を何にexportすればいいかわからない

~~~~
The type _≡_ cannot be translated to a Haskell type.
when checking the pragma COMPILED_EXPORT head' safeHead
~~~~

# COMPILED_EXPORTできない関数

* 型の中にexportできないシンボルが含まれているもの
    * Haskellに上手いマップの無いもの
        * 自然数型`ℕ`
    * GADT的なものなど
        * Propositional Equality `_≡_` による型
    * あまり単純じゃない型は大体ダメ

# どうする？

たとえばラップしたものをexport

~~~~
head' : ∀ {a} {A : Set a} (xs : List A) → Maybe A
head' = go where
  go : ∀ {a} {A : Set a} (xs : List A) → Maybe A
  go [] = nothing
  go (x ∷ xs) = just (head (x ∷ xs) {λ ()})
{-# COMPILED_EXPORT head' safeHead' #-}
~~~~

* `head`を直接使わない
* `head'`でラップ
    * 証明項が作れないものは`nothing`
    * 証明項が作れるものは`head`の結果を`just`

# Inductive/Coinductive Data Type の区別

HaskellにはListとColistの区別が無い！

~~~~
rev . rev = id
~~~~

~~~~
rev (rev 有限リスト) = id 有限リスト

~~~~

~~~~
rev (rev 無限リスト) = id 無限リスト ？

~~~~

アブナイ！

# ghc-mod/emacsが激重

生成モジュールをimportしたモジュールを開くとemacsが激重

* MAlonzoによる生成モジュールはwarningだらけ
    * ghc-modが1分程帰らない
    * その後，emacsがずっとCPU使用率100%
        * 何してるの？未調査

いまのところ**対策なし**

* 一応，重くなってしまったバッファを閉じれば…


# Agdaの関数をHaskellから使う編…結果

* できなくはない
* が，少々つらい
    * 無意味なラップが多い
        * exportされた関数のHaskell側でのラップ
        * 問題無くexportするためのAgda側でのラップ
        * ラップ方法が正しいかという問題
    * HaskellとAgdaの違いが無視される
    * emacsが重くてHaskellが書けない
* 初心者にオススメするのは少し難しいかもしれない

# まとめ

* Agdaで全て書く
    * 理想的
    * つらい
* Agdaの関数をHaskellから使う
    * 多少現実的
    * つらい

# 以上

本当はつらい Real World Agda でした．

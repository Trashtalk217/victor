# VICTOR

VICTOR is a program based on ['A Knowledge-based Approach of Connect-Four'](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.38.2778&rep=rep1&type=pdf) by Victor Allis. The original program written in C has been lost to history. This current implementation is written in Rust.

## Purpose

VICTOR can evaluate a connect four position and decide if black can draw or win the game, or if white can win the game. It can be used as follows:

```
$ ./target/release/victor_rs full-eval 34444445
score: -1, number of nodes: 1
```

Here, a score of -1 means that black can draw ensure themselves at least a draw. The string of numbers 3444445 represents a connect four position.

```
$ ./target/release/victor_rs show 34444445
...●...
...○...
...●...
...○...
...●...
..●○○..
White to play
```

In this case, the white player goes first and puts a disc in the third column from the right, the black plays in column 4 and white plays on top, again in column 4. This is how the string of numbers is interpreted, as a back and forth game between the white and black player.

## Architecture

VICTOR currently uses two evaluation phases, the knowledge evaluation and the conspiracy search. The paper first mentioned also described a depth first approach which is not yet implemented.

### Knowledge Evaluation

The knowledge evaluation phase takes a position and tries to 'solve' it using strategic rules. These rules come in the form of guarantees for particular empty squares. Take the position which we started with:

```
...●...
...○...
...●...
...○...
...●...
..●○○..
White to play
```

Black can employ a rule called *ClaimEven*. Which makes use of the fact that when white makes a move, black can immediately follow up playing on top of white. This rule ensures that black can get the following squares:

```
xxx●xxx
...○...
xxx●xxx
...○...
xx.●.xx
..●○○..
White to play
```

If we now check take a look at all the possible connect-fours for white, we see that all of them at least use one square that is claimed by black. This means that given perfect play for black, white can't make a connect four. Meaning that this position evaluates to -1, black can draw this game.

In the paper there are more examples of strategic rules with formal definitions. It also shows how those rules can and can't be combined to solve an entire board. It should be noted that knowledge evaluation sometimes falls short, and can't solve a position. This introduces the next evaluation phase: Conspiracy search.

### Conspiracy Search

Conspiracy search is a best-first tree search. It takes a position and if it can't be solved by the knowledge evaluation it generates all the possible positions that follow from it. Let's work through an example:

```
.......
.......
.......
.......
○○○....
●●●....
White to play
```

Here, It's very clear who is winning, but computers are not intelligent unless we make them. So we generate 7 new positions of which one is winning. After white sees that move is winning, white will play it and win. Making sure that the starting position evaluates to 1. If after just a singe expansion, no position is clearly winning, we have to expand the tree further. This happens recursively.

Conspiracy search dictates *how* we expand the tree, making sure that we visit promising variations first. Because of my limited understanding of conspiracy search, I cannot adequately explain how it works.

### Depth Search

The paper being adapted describes a third evaluation phase, a depth first search, which is not yet implemented in the code base, so I'll refrain from explaining it here.

## Shortfalls

There are a couple (many) things in this current code base that simply don't work at all or don't work as well as they should.

- The *SpecialBefore* rule doesn't work, and is not included in the knowledge evaluation.
- It's very likely that the threat combination rules don't fully work. As in, the knowledge evaluation should be able to handle more positions with a better threat combination implementation.
- There's a non-zero chance that my implementation of conspiracy search is wrong. I ran it against an alpha-beta search and it had a higher node count by a factor of at least two. That seems very weird.
- Optimization: The current implementation is slow, too slow. And it needs a lot of work. Mainly the knowledge evaluation can use a lot of work.
- General refactoring. This code is made with the idea that it's save-able, so it can be turned into decent code without a complete rework. Currently, it is not yet decent code.

## Intention

The original intention of this project was to make a faster connect four AI than the alpha-beta AI I previously made in Rust, following this [highly recommended tutorial](https://blog.gamesolver.org/solving-connect-four/01-introduction/). That AI was able to evaluate the starting position in about 4.5 minutes on my laptop. The current AI is not capable of that, and needs some work.

I also intent to do some academic reproduction with this study. Because I believe that code should be included in scientific papers, to make it easier for other researcher to build on, and test that code.

These two goals can be at odds. Making the AI faster might involve removing the conspiracy search from the code, making it less of a historical reproduction. The simplest solution is to create a historic branch in the git repository.

## Conclusion

I was once told that a piece of writing should include a conclusion. But I don't have one. If you want to work on this, it's very much appreciated and please contact me.

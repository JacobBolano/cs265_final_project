Bril: A Compiler Intermediate Representation for Learning
=========================================================

> This Max's fork of the Bril repo for teaching Berkeley's [CS 265](https://github.com/mwillsey/cs265).
> Links will likely still point to the published [Bril docs](https://capra.cs.cornell.edu/bril/).
> I will try to keep this compatible with the original Bril repo, so those docs should still be useful.

Bril (the Big Red Intermediate Language) is a compiler IR made for teaching Cornell's [CS 6120][cs6120], a grad compilers course.
It is an extremely simple instruction-based IR that is meant to be extended.
Its canonical representation is JSON, which makes it easy to build tools from scratch to manipulate it.

This repository contains the [documentation][docs], including the [language reference document][langref], and some infrastructure for Bril.
There are some quick-start instructions below for some of the main tools, but
check out the docs for more details about what's available.

[docs]: https://capra.cs.cornell.edu/bril/
[langref]: https://capra.cs.cornell.edu/bril/lang/index.html
[brilts]: https://github.com/sampsyo/bril/blob/master/bril-ts/bril.ts


Install the Tools
-----------------

The [`install.sh`](install.sh) script will install the tools for you.
Read it first to see what it does, then run it:

    $ ./install.sh

It installs the following tools (and their dependencies):
- [`brili`](https://capra.cs.cornell.edu/bril/tools/interp.html), the reference interpreter
- [`brilck`](https://capra.cs.cornell.edu/bril/tools/brilck.html), the type checker
- [`ts2bril`](https://capra.cs.cornell.edu/bril/tools/ts2bril.html), a TypeScript-to-Bril compiler
- [`bril2json` and `bril2txt`](https://capra.cs.cornell.edu/bril/tools/text.html), the JSON-to-text and text-to-JSON converters
- [`turnt`](https://github.com/cucapra/turnt), a snapshot-based testing tool (not specific to Bril, but used for the tests)
- [`brench`](https://capra.cs.cornell.edu/bril/tools/brench.html), the Bril benchmark runner.

Tests
-----

There are some tests in the `test/` directory.
They use [Turnt][], which lets us write the expected output for individual commands.
Install it with [pip][] or the `install.sh` script:

    $ pip3 install --user turnt

Then run all the tests by typing `make test`.

[pip]: https://packaging.python.org/tutorials/installing-packages/
[cs6120]: https://www.cs.cornell.edu/courses/cs6120/2020fa/
[turnt]: https://github.com/cucapra/turnt

## Write an optimizer!

Check out [examples/remove_nops](examples/remove_nops) for a simple, complete example of how to write an optimization pass for Bril.
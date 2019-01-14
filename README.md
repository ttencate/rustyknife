Rusty Knife
===========

Rusty Knife is a Rust implementation of the Inform Z-machine virtual machine,
which powers old Infocom games like Zork.

Goals
-----

* To create a Z-machine implementation that implemens Z-machine versions 1-3,
  and is fully compliant with the [Version 1.1
  specification](http://inform-fiction.org/zmachine/standards/z1point1/index.html).
* To implement save files in the portable
  [Quetzal](http://inform-fiction.org/zmachine/standards/quetzal/index.html)
  format.
* To write this in efficient, self-documenting, well-tested, idiomatic Rust code.
* To add frontends for the command line, IRC and the web (via WebAssembly).

Non-goals (for now)
-------------------

* To implement anything beyond Z-machine version 3. That said, any features
  that are not common to all versions will be guarded by a `match` block. So if
  a new version number is added, the compiler will point out all the places
  that need extra code. Additionally, [this table by Hans
  Prestige](https://hansprestige.com/inform/zmachine_versions.html) will be
  very useful to find out what changes between versions.
* To compete with existing Z-machine implementations like Frotz.

Status
------

* Most functionality of the Z-machine versions 1-3 has been implemented.
* It passes the CZECH and strictz test suites (insofar applicable to Z-machine
  version 3).
* There is a very simple console-line based version, which reads from standard
  input and prints to standard output.
* Zork seems to run.

To be done:

* Saving and restoring
* Screen splitting
* IRC bot
* WebAssembly version and JavaScript wrapper

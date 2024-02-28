## Binds cheatsheet
### Top level
| action               | vscode  |
|----------------------|---------|
| Reload and typecheck | C-c C-l |
| Restart Agda         | C-c C-r |
| Compute expression   | C-c C-n |

### In hole
| action                                             | vscode    |
|----------------------------------------------------|-----------|
| [Auto] (`agsy`)                                    | C-c C-a   |
| Ask for goal, and context                          | C-c C-,   |
| Ask for goal, context, and expression in hole      | C-c C-.   |
| Try to use given expr to fill hole ("give")        | C-c C-SPC |
| Introduce arguments                                | C-c C-c   |
| Case split (asks for input or names in the hole)   | C-c C-c   |
| Introduce [copattern] (don't enter a name)         | C-c C-c   |
| Attempt to introduce "constructor"\* ("refine")    | C-c C-r   |
| Try to use function in hole, adding holes for args | C-c C-r   |

For Emacs, the [official documentation](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html) is plenty good.

For vim with Cornelis, there are no official bindings, but there are some recommendations in its README.

#### \* "constructor" here means a couple of things
  * literally a constructor for a type, whose types matches - if ambiguous, the refine won't succeed
  * a lambda with as many arguments as possible - this is kind of a constructor if you squint or if you want to be technical, for the function type (`->`)
  * a record with the required fields for the current type, with holes for the field values
  * **!VERY USEFUL! - if you have a function name in the hole, if the return type matches the goal, the function will be introduced with holes for its arguments**

## Video lectures playlists

### [This semester's](https://www.youtube.com/watch?v=lsxovC6bloM&list=PLShxdZq0K256lRgLZTi6e6KouExs5ZEV4&pp=gAQBiAQB)

### [Last time's](https://www.youtube.com/watch?v=s5IBp2IwSw4&list=PLShxdZq0K256pGsUNHtvDux3Qbzu2ZWXI&pp=gAQBiAQB)

## [Agda installation instructions](./agda_install_instructions.md)

## Editor integrations

#### [Emacs](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)

This is the official, first, and likely most supported editor integration
#### [vscode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode)

This is probably the easiest integration to use.
#### [vim](https://github.com/isovector/cornelis/)

Note that you might need the latest Agda for this.

## Resources

### [Recordings of lectures (in Bulgarian)](https://www.youtube.com/playlist?list=PLShxdZq0K256pGsUNHtvDux3Qbzu2ZWXI)


### Other materials
Some git repos for agda courses:
* https://github.com/pigworker/CS410-17
* https://github.com/pigworker/CS410-18

Nice exercises and approach (imo), with the huge bonus of having recorded [video lectures](https://github.com/pigworker/CS410-17#lecture-videos-on-youtube).

[PLFA](https://plfa.github.io/) - A loose adaptation of the [popular Coq based book](https://softwarefoundations.cis.upenn.edu/) to Agda.

Good for a gentle introduction, and some exercises. Also for lambda calculus related things in Agda.

## `Agda` in a browser
You can get a set up emacs agda environment in your browser at this website:
https://agdapad.quasicoherent.io/

Additionally, if you send someone the link to the same session, you can work together.

[copattern]: https://agda.readthedocs.io/en/latest/language/copatterns.html
[Auto]: https://agda.readthedocs.io/en/latest/tools/auto.html

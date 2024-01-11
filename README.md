## Various useful bits of information

### Building `doc-gen4` pages

```sh
lake -R -Kenv=dev update # perhaps not so useful
lake -R -Kenv=dev build RMT4:docs
(cd .lake/build/doc ; python3 -m http.server)
```
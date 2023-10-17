# The Capy Standard Library

This contains the basic functionality needed for any good program. It will automatically be downloaded from GitHub if it does not exist in the modules directory (`/capy/modules` by default)

You can import any module with the `mod` keyword

```capy
core :: mod "core";
```

It will search the modules directory for a folder named "core" which contains a `mod.capy`.

Note the distinction between `mod` and `import`. `import` is specifically for local project files.

```capy
server :: import "server.capy";
```

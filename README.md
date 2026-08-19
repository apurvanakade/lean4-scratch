# scratch

A Lean 4 project (depending on Mathlib) for scratch/exercise files.

## Running locally

These steps get you from a fresh machine to editing and building this project in VS Code.

### 1. Install Visual Studio Code

Download and install VS Code from [code.visualstudio.com](https://code.visualstudio.com/). On macOS, drag `Visual Studio Code.app` into your `Applications` folder, then launch it.

### 2. Install the Lean 4 extension

1. Open VS Code.
2. Click the Extensions icon in the left sidebar (or press `Cmd+Shift+X` on macOS / `Ctrl+Shift+X` on Windows/Linux).
3. Search for **"lean4"** and install the extension published by **leanprover** (marketplace id `leanprover.lean4`).

This extension provides Lean syntax highlighting, the interactive goal/tactic state view, and (on first use) will offer to install `elan`, the Lean toolchain version manager, if it isn't already on your machine.

### 3. Install `elan` (Lean toolchain manager)

If the extension didn't already install it for you, install `elan` manually:

- **macOS/Linux**, in a terminal:
  ```sh
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```
- **Windows**: download and run the installer from the [elan releases page](https://github.com/leanprover/elan/releases).

Restart your terminal (and VS Code) afterwards so the `elan`/`lake`/`lean` commands are on your `PATH`. Verify with:

```sh
elan --version
lake --version
```

### 4. Clone this repository

```sh
git clone <this-repo-url> scratch
cd scratch
```

### 5. Open the project in VS Code

```sh
code .
```

Because this folder contains a [lean-toolchain](lean-toolchain) file, `elan` will automatically download and use the exact Lean version pinned there (currently `leanprover/lean4:v4.32.2`) the first time you build or open a `.lean` file — no manual version selection needed.

### 6. Fetch the prebuilt Mathlib cache

This project depends on [Mathlib](https://github.com/leanprover-community/mathlib4), which is large to build from source. Fetch prebuilt `.olean` files instead of compiling Mathlib yourself:

```sh
lake exe cache get
```

### 7. Build the project

```sh
lake build
```

### 8. Start editing

Open any file under [Scratch/](Scratch/) (or [Scratch.lean](Scratch.lean)) in VS Code. Give the Lean 4 extension a moment to load the file's imports — the status bar shows a spinner while it processes — then you'll get live goal states, hover info, and error checking as you edit.

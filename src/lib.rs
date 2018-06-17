//! The Cheddar shading language.
//!
//! # Foreword
//!
//! Cheddar is a superset of [GLSL](https://en.wikipedia.org/wiki/OpenGL_Shading_Language) that adds
//! several features to augment GLSL:
//!
//!   - Some non-valid GLSL constructions made valid in Cheddar to ease the writing of certain
//!     shader stages.
//!   - A more [functional](https://en.wikipedia.org/wiki/Functional_programming) approach to
//!     programming shaders on the GPU.
//!   - Structures, types and GLSL-specific constructs sharing.
//!   - Imports and modules.
//!
//! # A functional shading language
//!
//! Cheddar uses – for most constructs – the same syntax as GLSL. If you’ve been writing GLSL for a
//! while, you’ll need something like twenty minutes to get your feet wet with Cheddar and start
//! being productive with it.
//!
//! The biggest change from GLSL is that Cheddar tries to be more functional. It’s still an
//! imperative language; you can still create variable and mutably change their content. However,
//! you don’t write to globals anymore (i.e. vertex attributes) or you don’t *emit* vertices and
//! primitives anymore.
//!
//! ## The core: the semantics functions
//!
//! *Semantics functions* are functions you can declare that have a name that makes them special.
//! Every programmer knows at least one semantics function: `main`. If an *unit of code* exports a
//! function named `main` taking no argument and returning nothing, this function will be treated as
//! the *entry point* of your binary for example. Cheddar uses this concept by recognizing several
//! semantics functions.
//!
//! > Note: it’s possible to change the name of the function that a linker / compiler recognizes as
//! > the `start` routine. This is not currently possible with Cheddar, though.
//!
//! Most of the semantics functions directly map to *shader stages*. With vanilla GLSL, if you want
//! to write a *vertex shader*, you must provide a unit of code that provide a `main` function. That
//! code will typically read *vertex attributes* via `in` declarations and will pass code to the
//! next stage (typically a *fragment shader*, but it might be a *geometry shader* too, for
//! instance).
//!
//! This is a typical, boring *vertex shader*:
//!
//! ```ignore
//! layout (location = 0) in vec3 i_pos;
//! layout (location = 1) in vec4 i_col;
//!
//! in vec4 o_col;
//!
//! void main() {
//!   gl_Position = vec4(i_pos, 1.);
//!   o_col = i_col;
//! }
//! ```
//!
//! This simple *vertex shader* simply passes its color to the next stage.
//!
//! Now let’s try to convert this snippet to Cheddar. First thing first, Cheddar doesn’t have the
//! concept of a *shader stage*. Everything is a function. This enables better composition. The
//! semantics function that maps to a *vertex shader* is the `map_vertex` function in Cheddar. Some
//! rules and laws must be respected:
//!
//!   - The signature of `map_vertex` is free, but:
//!     - It must return a user-defined type, which name is free.
//!     - It can have as many arguments as you want (even zero), that represent the inputs of the
//!       vertex shader. However, the types of those arguments must be compatible with GLSL vertex
//!       attributes.
//!     - If you want to ignore an argument, you can just omit its name but keep its type (like you
//!       would do in C for instance).
//!   - The type in return position must have at least one field which type is `vec4` – its name is
//!     free. This field represents the actual position of the computed output vertex.
//!
//! Cheddar doesn’t care about the order in which the functions and types appear, it will
//! re-organize them when compiling.
//!
//! The Cheddar for the snippet above could be:
//!
//! ```ignore
//! struct V {
//!   vec4 pos;
//!   vec4 col;
//! };
//!
//! V map_vertex(vec3 pos, vec4 col) {
//!   return V(vec4(pos, 1.), col);
//! }
//! ```
//!
//! When compiled to GLSL, this Cheddar code will look like the former GLSL snippet above. You can
//! see several interesting properties:
//!
//!   - Globals (i.e. `in`) don’t exist anymore and are now **function arguments**.
//!   - You can ignore function arguments – e.g. `V map_vertex(vec3 pos, vec4)`.
//!   - You don’t write to globals (i.e. `out`) anymore but **return values**.
//!
//! In that sense, Cheddar is more functional than vanilla GLSL.
//!
//! You will want to write a *fragment shader* to consume that `color` value. The principle is
//! exactly the same: you need to write a semantics function that will accept this `V` type as
//! **single argument** and return a user-defined type. This function must be named `map_frag_data`.
//!
//! Let’s write a fragment shader that will display our vertices by using *vertices’ colors*:
//!
//! ```
//! struct F {
//!   vec4 col;
//! };
//!
//! F map_frag_data(V v) {
//!   return F(v.col);
//! }
//! ```
//!
//! That’s all! Finally, imagine that we want to insert a *geometry shader* between the *vertex
//! shader* and the *fragment shader*. This is done by defining the `concat_map_prim`. This function
//! is tricky because it returns nothing and acts as a
//! [generator](https://en.wikipedia.org/wiki/Generator_(computer_programming)). It takes two
//! arguments:
//!
//!   - The input patch type, in the form `in YourType[dimension] binding_name`.
//!     - `YourType` is your defined vertex type (in our case, it’d be `V`).
//!     - `dimension` is the number of vertices in the patch:
//!       - `1` will make you map over points.
//!       - `2` will make you map over lines.
//!       - `3` will make you map over triangles.
//!     - `binding_name` is whatever you want the argument to be called.
//!   - The output primitive type, in the form `layout (output_prim, max_vertices = nb) out YourOutputType`.
//!     - `output_prim` is the output primitive to use.
//!       - `points` will output simple points.
//!       - `line_strip` will output strip lines.
//!       - `triangle_strip` will output strip triangles.
//!     - `nb` is the maximum number of vertices you’ll output.
//!
//! Here’s an example for our current example:
//!
//! ```ignore
//! struct GV {
//!   vec4 pos;
//!   vec4 col;
//!   vec3 normal;
//! };
//! void concat_map_prim(in V[3] verts, layout (triangle_strip, max_vertices = 3) out GV) {
//!   // …
//! }
//! ```
//!
//! Then the next thing you want to know is how you’re supposed to “generate” vertices and
//! primitives. This is done by a set of semantics functions:
//!
//!   - `yield_vertex`, which takes as single argument the type of input vertex (`V` in our case).
//!   - `yield_primitive`, which doesn’t take any argument.
//!
//! Both the function return nothing. The former will *yield* the vertex you pass as argument and
//! will send it to the current primitive. Strip primitives will then connect every vertex you yield
//! until you call the `yield_primitive` function, that will yield the primitive with the previous
//! points and eventually start another primitive if you issue other `yield_vertex` calls
//! afterwards.
//!
//! Finally, those functions are to be put in the same code unit. Cheddar doesn’t require you to
//! pass different strings for different *shader stages* since the semantics functions have
//! different signatures and names.
//!
//! # Constructs sharing
//!
//! One major advantage of Cheddar is to enable *constructs sharing*. That is, most global symbols
//! you use are shared between all the *shader stages*. This is not very surprising since we’ve been
//! only defining functions so far, so why would we need to duplicate every types we used? Even
//! though GLSL require you to duplicate `struct`, `uniform` and `in` / `out` declarations, Cheddar
//! doesn’t and will perform everything under the hoods.
//!
//! If you declare a type, such as:
//!
//! ```ignore
//! struct MySuperCoolType {
//!   float a;
//!   vec3 b;
//!   mat4 c;
//! };
//! ```
//!
//! And use it in several semantics functions (let’s say `map_vertex` and `map_frag_data`), Cheddar
//! will automatically generate the *vertex shader* and the *fragment shader* with the same type
//! definition for `MySuperCoolType`.
//!
//! This sharing is active for:
//!
//!   - `struct` definition.
//!   - Global `const` declarations. You’ll love defining `PI` once and for all!
//!   - `uniform` (both regular and *blocks*).
//!   - You don’t have to worry about `in` and `out` matching since everything is done at the
//!     function level and through your defined types.
//!   - Any function other than the semantics functions.
//!
//! # Modules and imports
//!
//! ## Definition
//!
//! Cheddar also comes with a mandatory features for refactoring and organizing one’s code: modules.
//! Any piece of code you write belong to a module. For now, modules export all of the symbols
//! defined in them.
//!
//! A module has a name and it must be unique. The name has the form: `foo.bar.zoo` and has a direct
//! filesystem representation. Here, the `foo.bar.zoo` module lives in the file at
//! `foo/bar/zoo.chdr`.
//!
//! ## Importing a module
//!
//! A module can be imported with the `use` keyword – easy, same as Rust! – and items can be picked
//! by enclosing them in `( )`:
//!
//! ```ignore
//! use foo.bar.zoo (PI)
//! ```
//!
//! Here, we import `PI` from `foo.bar.zoo`.
//!
//! > Disclaimer: currently, the *import list* is just a hint to the programmer and is not used by
//! > the Cheddar runtime. Every symbols are imported. This will be fixed in a future release.
//!
//! Cheddar supports transitive dependency and knows how to resolve the *diamond problem* for
//! imports. It will also correctly catch dependency 
//!
//! # Note on validation
//!
//! Currently, Cheddar does a very, very minimal job at validating your code. It checks, mostly:
//!
//!   - The GLSL syntax via the [glsl](https://crates.io/crates/glsl) crate.
//!   - Some Cheddar constructs, like the types you provide or the fields in the vertex type, for
//!     instance.
//!   - Dependency module cycles.
//!
//! The **semantics of your code is not analyzed**. That means that if you do something like
//! `float x = true;`, Cheddar won’t complain.
//!
//! Development to fix this are on the go but contribution is highly welcomed.

extern crate glsl;
#[macro_use]
extern crate nom;
extern crate warmy;

pub mod error;
pub mod lang;
pub mod parser;

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
//! The language is presented as an EDSL.
//!
//! # A functional shading language
//!
//! Cheddar uses – for most constructs – the same syntax as GLSL. If you’ve been writing GLSL for a
//! while, you’ll need something like twenty minutes to get your feet wet with Cheddar and start
//! being productive with it.
//!
//! The biggest change from GLSL is that Cheddar tries to be more functional. It’s still an
//! imperative language; you can still create variables and mutably change their content. However,
//! you don’t write to globals anymore (i.e. vertex attributes) or you don’t *emit* vertices and
//! primitives anymore.
//!
//! ## The core: the semantics functions
//!
//! *Semantics functions* are functions you can declare that have a name that makes them special.
//! Every programmer knows at least one semantics function: `main`. If a *unit of code* exports a
//! function named `main` taking no argument and returning nothing, this function will be treated as
//! the *entry point* of your binary for example. Cheddar uses this concept by recognizing several
//! semantics functions.
//!
//! > Note: it’s possible to change the name of the function that a linker / compiler recognizes as
//! > the `start` routine. This is not currently possible with Cheddar, though.
//!
//! Most of the semantics functions directly map to *shader stages*. With vanilla GLSL, if you want
//! to write a *vertex shader*, you must provide a unit of code that exports a `main` function. That
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
//!     currently restricted and you must call it `chdr_Position`. This field represents the actual
//!     position of the computed output vertex and you won’t be able to read from it; you can only
//!     write to it. If you need it after `map_vertex`, you need to add another field to your
//!     struct. This limitation might be removed in a future release.
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
//!
//! void concat_map_prim(in V[3] verts, layout (triangle_strip, max_vertices = 3) out GV) {
//!   // …
//! }
//! ```
//!
//! Then the next thing you want to know is how you’re supposed to “generate” vertices and
//! primitives. This is done by a set of semantics functions:
//!
//!   - `yield_vertex`, which takes as single argument a vertex correctly typed (`V` in our case).
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
//! Cheddar supports transitive dependencies and knows how to resolve the *diamond problem* for
//! imports. It will also correctly catch dependency cycles, if you come accross any.
//!
//! ### Note on `warmy`
//!
//! Cheddar uses the `warmy` crate to provide you with modules and a simple dependency solver.
//! The current situation is that Cheddar will not lookup the dependency of your module if you don’t
//! ask it to do so. See the [`Module::substitute_imports`] function for further information on how
//! to do so.
//!
//! Because of using `warmy`, Cheddar also supports automatic live reloading the shading modules.
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
//! Development to fix this is on the go but contributions are highly welcomed!
//!
//! # Note on tessellation control and evaluation shaders
//!
//! Those two stages are yet to be integrated into Cheddar.

#![feature(box_syntax)]
#![feature(box_patterns)]

extern crate glsl;
#[macro_use]
extern crate nom;
extern crate warmy;

use glsl::syntax::*;
pub use glsl::parser::{ParseError, ParseResult};
use glsl::parser;
use glsl::parsers::{external_declaration, identifier};
use glsl::transpiler;
use nom::alphanumeric;
use std::collections::HashSet;
use std::error::Error;
use std::fmt::{self, Write};
use std::fs::File;
use std::io::Read;
use std::iter::once;
use std::path::PathBuf;
use std::str::from_utf8_unchecked;
use warmy::{FSKey, Load, Loaded, Res, Storage};

/// GLSL AST.
pub type GLSL = Vec<ExternalDeclaration>;

/// Parse a Cheddar source from a bytes stream.
pub fn parse<S>(source: S) -> ParseResult<Module> where S: AsRef<[u8]> {
  parser::parse(source.as_ref(), module)
}

/// Parse a Cheddar source from a string.
pub fn parse_str<S>(source: S) -> ParseResult<Module> where S: AsRef<str> {
  parser::parse_str(source.as_ref(), module)
}

/// A module.
///
/// A module has a list of imports and a list of GLSL extern declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct Module {
  /// List of imports for this module.
  pub imports: Vec<ImportList>,
  /// The GLSL body of the module.
  pub glsl: GLSL
}

impl Module {
  /// Shrink a module along with its imports to yield a bigger module with no import. Return all
  /// the visited modules (including the current one).
  ///
  /// This is needed whenever the module must be compiled to strings (i.e. [Module::to_glsl_setup]).
  pub fn substitute_imports<C>(
    &self,
    current_key:
    &FSKey,
    storage:
    &mut Storage<C>,
    ctx: &mut C
  ) -> Result<(Self, Vec<FSKey>), ModuleError>
  where C: 'static {
    let mut visited = HashSet::new(); // already visited modules
    let mut parents = HashSet::new(); // modules from which we come; used to detect import cycles
    let mut glsl = Vec::new();

    self.rec_substitute_imports(current_key, storage, ctx, &mut visited, &mut parents, &mut glsl)?;

    let module = Module { imports: Vec::new(), glsl };
    let dep_keys = visited.into_iter().collect();

    Ok((module, dep_keys))
  }

  /// Recursively substitute the imports from a module.
  ///
  /// This function will accumulate some GLSL code by performing a DFS on the dependency DAG. It is
  /// dependency-cycle-aware and handles transitive dependency without duplication.
  fn rec_substitute_imports<C>(
    &self,
    current_key: &FSKey,
    storage: &mut Storage<C>,
    ctx: &mut C,
    visited: &mut HashSet<FSKey>,
    parents: &mut HashSet<FSKey>,
    glsl: &mut GLSL
  ) -> Result<(), ModuleError>
  where C: 'static {
    parents.insert(current_key.clone());
    visited.insert(current_key.clone());

    for il in &self.imports {
      let path = il.to_path();
      let key = FSKey::new(&path);

      // ensure this module is not a parent (break dependency cycle)
      if parents.contains(&key) {
        return Err(ModuleError::DepsError(DepsError::Cycle(current_key.clone(), key.clone())));
      }

      // do not treat already visited modules (prevent from GLSL duplication)
      if visited.contains(&key) {
        continue;
      }

      // borrow the module and recursively call this function to get all the GLSL chain
      let module: Res<Self> = storage.get(&key, ctx).map_err(|e| ModuleError::DepsError(DepsError::LoadError(key.clone(), box e)))?;
      module.borrow().rec_substitute_imports(&key, storage, ctx, visited, parents, glsl)?;
    }

    glsl.extend(self.glsl.iter().cloned());

    parents.remove(current_key);

    Ok(())
  }

  /// Fold a module into its GLSL setup.
  pub fn to_glsl_setup(&self) -> Result<ModuleFold, GLSLConversionError> {
    let uniforms = self.uniforms();
    let blocks = self.blocks();
    let structs = self.structs();
    let functions = self.functions();
    let globals = self.globals();

    let mut common = String::new();
    let mut vs = String::new();
    let mut gs = String::new();
    let mut fs = String::new();
    let mut structs_str = String::new();

    // sink uniforms, blocks, constants and functions as a common framework
    for uniform in &uniforms {
      transpiler::glsl::show_single_declaration(&mut common, uniform);
      let _ = common.write_str(";\n");
    }

    for block in &blocks {
      transpiler::glsl::show_block(&mut common, block);
      let _ = common.write_str(";\n");
    }

    for global in &globals {
      transpiler::glsl::show_single_declaration(&mut common, global);
      let _ = common.write_str(";\n");
    }

    for f in filter_out_special_functions(functions.iter()) {
      transpiler::glsl::show_function_definition(&mut common, f)
    }

    let mut filter_out_struct_def = Vec::new();

    // get the special functions
    let map_vertex = functions.iter().find(|fd| &fd.prototype.name == "map_vertex")
                                     .ok_or(GLSLConversionError::NoVertexShader)?;
    let concat_map_prim = functions.iter().find(|fd| &fd.prototype.name == "concat_map_prim");
    let map_frag_data = functions.iter().find(|fd| &fd.prototype.name == "map_frag_data")
                                        .ok_or(GLSLConversionError::NoFragmentShader)?;

    // sink the vertex shader
    let (vertex_ret_ty, vertex_outputs) = sink_vertex_shader(&mut vs, map_vertex, &structs)?;

    filter_out_struct_def.push(vertex_ret_ty.name.clone());

    // if there’s any, sink the geometry shader and get its return type – it’ll be passed to the
    // fragment shader; otherwise, just return the vertex type
    let (fs_prev_ret_ty, fs_prev_outputs) = if let Some(concat_map_prim) = concat_map_prim {
      let (ret_ty, outputs) = sink_geometry_shader(&mut gs,
                                                   &concat_map_prim,
                                                   &structs,
                                                   &vertex_ret_ty,
                                                   &vertex_outputs)?;

      filter_out_struct_def.push(ret_ty.name.clone());
      (ret_ty, outputs)
    } else {
      (vertex_ret_ty, vertex_outputs)
    };

    // sink the fragment shader
    let (fragment_ret_ty, _) = sink_fragment_shader(&mut fs,
                                                    &map_frag_data,
                                                    &structs,
                                                    &fs_prev_ret_ty,
                                                    &fs_prev_outputs)?;

    filter_out_struct_def.push(fragment_ret_ty.name.clone());

    // filter out structs that might only exist in specific stages
    for s in &structs {
      if !filter_out_struct_def.contains(&s.name) {
        transpiler::glsl::show_struct(&mut structs_str, s);
      }
    }

    common = structs_str + &common;

    if vs.is_empty() {
      Err(GLSLConversionError::NoVertexShader)
    } else if fs.is_empty() {
      Err(GLSLConversionError::NoFragmentShader)
    } else {
      let setup = ModuleFold {
        vs: common.clone() + &vs,
        gs: if gs.is_empty() { None } else { Some(gs.clone()) },
        fs: common.clone() + &fs
      };

      Ok(setup)
    }
  }

  /// Get all the uniforms defined in a module.
  fn uniforms(&self) -> Vec<SingleDeclaration> {
    let mut uniforms = Vec::new();

    for glsl in &self.glsl {
      if let ExternalDeclaration::Declaration(Declaration::InitDeclaratorList(ref i)) = *glsl {
        if let Some(ref q) = i.head.ty.qualifier {
          if q.qualifiers.contains(&TypeQualifierSpec::Storage(StorageQualifier::Uniform)) {
            uniforms.push(i.head.clone());

            // check whether we have more
            for next in &i.tail {
              uniforms.push(SingleDeclaration {
                ty: i.head.ty.clone(),
                name: Some(next.name.clone()),
                array_specifier: next.array_specifier.clone(),
                initializer: None
              })
            }
          }
        }
      }
    }

    uniforms
  }

  /// Get all the blocks defined in a module.
  fn blocks(&self) -> Vec<Block> {
    self.glsl.iter().filter_map(|ed| {
      match *ed {
        ExternalDeclaration::Declaration(Declaration::Block(ref b)) =>
          Some(b.clone()),
        _ => None
      }
    }).collect()
  }

  /// Get all the functions.
  fn functions(&self) -> Vec<FunctionDefinition> {
    self.glsl.iter().filter_map(|ed| match *ed {
      ExternalDeclaration::FunctionDefinition(ref def) => Some(def.clone()),
      _ => None
    }).collect()
  }

  /// Get all the declared structures.
  fn structs(&self) -> Vec<StructSpecifier> {
    self.glsl.iter().filter_map(|ed| {
      match *ed {
        ExternalDeclaration::Declaration(
          Declaration::InitDeclaratorList(
            InitDeclaratorList {
              head: SingleDeclaration {
                ty: FullySpecifiedType {
                  ty: TypeSpecifier {
                    ty: TypeSpecifierNonArray::Struct(ref s),
                    ..
                  },
                  ..
                },
                ..
              },
              ..
            }
            )
          ) => Some(s.clone()),
        _ => None
      }
    }).collect()
  }

  /// Get all the globals.
  fn globals(&self) -> Vec<SingleDeclaration> {
    let mut consts = Vec::new();

    {
      let mut push_const = |i: &InitDeclaratorList| {
        consts.push(i.head.clone());

        // check whether we have more
        for next in &i.tail {
          consts.push(SingleDeclaration {
            ty: i.head.ty.clone(),
            name: Some(next.name.clone()),
            array_specifier: next.array_specifier.clone(),
            initializer: None
          });
        }
      };

      for glsl in &self.glsl {
        if let ExternalDeclaration::Declaration(Declaration::InitDeclaratorList(ref i)) = *glsl {
          if let TypeSpecifierNonArray::Struct(_) = i.head.ty.ty.ty {
            // discard struct declaration
            continue;
          }

          if let Some(ref q) = i.head.ty.qualifier { // if we have at least one qualifier
            match q.qualifiers.as_slice() {
              &[TypeQualifierSpec::Storage(StorageQualifier::Const)] => {
                push_const(i);
              }

              _ => ()
            }
          } else { // no qualifier is a hacky global, but some GLSL implementations allow it…
            push_const(i);
          }
        }
      }
    }

    consts
  }
}

impl<C> Load<C> for Module {
  type Key = FSKey;

  type Error = ModuleError;

  fn load(key: Self::Key, _: &mut Storage<C>, _: &mut C) -> Result<Loaded<Self>, Self::Error> {
    let path = key.as_path();

    let mut fh = File::open(path).map_err(|_| ModuleError::FileNotFound(path.into()))?;
    let mut src = String::new();
    let _ = fh.read_to_string(&mut src);

    match parser::parse_str(&src[..], module) {
      ParseResult::Ok(module) => {
        Ok(module.into())
      }

      ParseResult::Err(e) => Err(ModuleError::ParseFailed(e)),

      _ => Err(ModuleError::IncompleteInput)
    }
  }
}


/// A non-empty import list.
///
/// It consists of a module path, like `Foo.Bar.Zoo`, and a list of symbols to load from that path,
/// as in `rick, marty, doggo`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportList {
  /// The module path to load symbols from.
  pub module: ModulePath,
  /// List of symbols to import.
  pub list: Vec<ModuleSymbol>
}

impl ImportList {
  /// Generate a [PathBuf] that represents this import on disk.
  pub fn to_path(&self) -> PathBuf {
    PathBuf::from(self.module.path.join("/") + ".chdr")
  }
}

/// A module path is a non-empty list of module(s), representing a hierarchy.
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct ModulePath {
  /// Hierarchical path of modules leading to the module we want to import (included in the path).
  pub path: Vec<ModuleName>
}

/// Name of a module.
pub type ModuleName = String;

/// A symbol, living in a module.
pub type ModuleSymbol = String;

/// Expected number of arguments type helper.
pub type ExpectedNumberOfArgs = usize;

/// Found number of arguments type helper.
pub type FoundNumberOfArgs = usize;

/// GLSL conversion error.
///
/// Such an errors can happen when a module is ill-formed.
#[derive(Clone, Debug, PartialEq)]
pub enum GLSLConversionError {
  /// No vertex shader was found. A vertex shader is required in order to build a shading pipeline.
  NoVertexShader,
  /// No fragment shader was found. A fragment shader is required in order to build a shading pipeline.
  NoFragmentShader,
  /// The output must not have a qualifier.
  OutputHasMainQualifier,
  /// The returned value must not be a struct.
  ReturnTypeMustBeAStruct(TypeSpecifier),
  /// The first field has the wrong type.
  WrongOutputFirstField(StructFieldSpecifier),
  /// The field of a type used as output cannot be a struct.
  ///
  /// This variant also gives the index of the field.
  OutputFieldCannotBeStruct(usize, StructSpecifier),
  /// The field of a type used as output cannot be a type name.
  ///
  /// This variant also gives the index of the field.
  OutputFieldCannotBeTypeName(usize, TypeName),
  /// The field of a type used as output cannot have several identifiers (only one).
  ///
  /// This variant also gives the index of the field.
  OutputFieldCannotHaveSeveralIdentifiers(usize, StructFieldSpecifier),
  /// The input type is unknown.
  UnknownInputType(TypeName),
  /// Wrong number of arguments.
  WrongNumberOfArgs(ExpectedNumberOfArgs, FoundNumberOfArgs),
  /// The type is not a required type name.
  NotTypeName,
  /// The geometry input is wrong.
  WrongGeometryInput,
  /// The geometry input’s dimension is wrong.
  WrongGeometryInputDim(usize),
  /// The geometry output layout is wrong.
  WrongGeometryOutputLayout(Option<TypeQualifier>)
}

impl fmt::Display for GLSLConversionError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      GLSLConversionError::NoVertexShader => {
        f.write_str("no vertex shader")
      }

      GLSLConversionError::NoFragmentShader => {
        f.write_str("no fragment shader")
      }

      GLSLConversionError::OutputHasMainQualifier => {
        f.write_str("output has main qualifier(s)")
      }

      GLSLConversionError::ReturnTypeMustBeAStruct(_) => {
        write!(f, "return type is not a struct")
      }

      GLSLConversionError::WrongOutputFirstField(_) => {
        write!(f, "first field’s type is forbidden as output")
      }

      GLSLConversionError::OutputFieldCannotBeStruct(idx, _) => {
        write!(f, "output field {} cannot be a struct", idx)
      }

      GLSLConversionError::OutputFieldCannotBeTypeName(idx, _) => {
        write!(f, "output field {} cannot be a type name", idx)
      }

      GLSLConversionError::OutputFieldCannotHaveSeveralIdentifiers(idx, _) => {
        write!(f, "output field {} cannot have several identifiers", idx)
      }

      GLSLConversionError::UnknownInputType(ref ty) => {
        write!(f, "unknown input type {}", ty)
      }

      GLSLConversionError::WrongNumberOfArgs(expected, found) => {
        write!(f, "expected {} arguments, found {}", expected, found)
      }

      GLSLConversionError::NotTypeName => {
        f.write_str("not a type name")
      }

      GLSLConversionError::WrongGeometryInput => {
        f.write_str("wrong geometry input")
      }

      GLSLConversionError::WrongGeometryInputDim(dim) => {
        write!(f, "wrong geometry input’s dimension {}", dim)
      }

      GLSLConversionError::WrongGeometryOutputLayout(_) => {
        f.write_str("wrong geometry output layout")
      }
    }
  }
}

impl Error for GLSLConversionError {}

/// Errors that can happen in dependencies.
#[derive(Debug)]
pub enum DepsError {
  /// If a module’s dependencies has any cycle, the dependencies are unusable and the cycle is
  /// returned.
  Cycle(FSKey, FSKey),
  /// There was a loading error of a module.
  LoadError(FSKey, Box<Error>),
}

impl fmt::Display for DepsError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      DepsError::Cycle(ref a, ref b) => {
        write!(f, "module cycle beetwen {} and {}", a.as_path().display(), b.as_path().display())
      }

      DepsError::LoadError(ref path, ref e) => {
        write!(f, "error in {}: {}", path.as_path().display(), e)
      }
    }
  }
}

impl Error for DepsError {
  fn cause(&self) -> Option<&Error> {
    match *self {
      DepsError::LoadError(_, ref e) => Some(e.as_ref()),
      _ => None
    }
  }
}

/// Error that might happen while loading a [`Module`].
#[derive(Debug)]
pub enum ModuleError {
  FileNotFound(PathBuf),
  ParseFailed(ParseError),
  IncompleteInput,
  DepsError(DepsError)
}

impl fmt::Display for ModuleError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      ModuleError::FileNotFound(ref path) => {
        write!(f, "cannot find {}", path.display())
      }

      ModuleError::ParseFailed(ref e) => {
        write!(f, "parse error: {}", e)
      }

      ModuleError::IncompleteInput => {
        f.write_str("incomplete input")
      }

      ModuleError::DepsError(ref e) => {
        write!(f, "dependency error: {}", e)
      }
    }
  }
}

impl Error for ModuleError {
  fn cause(&self) -> Option<&Error> {
    match *self {
      ModuleError::ParseFailed(ref e) => Some(e),
      ModuleError::DepsError(ref e) => Some(e),
      _ => None
    }
  }
}

/// Module fold (pipeline).
///
/// When a module contains all the required functions and structures to define a workable pipeline,
/// it can be folded down to this type, that will be used by lower layers (GPU).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleFold {
  pub vs: String,
  pub gs: Option<String>,
  pub fs: String
}

/// Sink single declarations as external declarations.
fn sink_single_as_ext_decls<'a, F, I>(sink: &mut F, s: I)
                                      where I: IntoIterator<Item = &'a SingleDeclaration>,
                                            F: Write {
  for sd in s {
    let ed = single_to_external_declaration(sd.clone());
    transpiler::glsl::show_external_declaration(sink, &ed);
  }
}

/// Turn a `SingleDeclaration` into an `ExternalDeclaration`.
fn single_to_external_declaration(sd: SingleDeclaration) -> ExternalDeclaration {
  ExternalDeclaration::Declaration(
    Declaration::InitDeclaratorList(
      InitDeclaratorList {
        head: sd,
        tail: Vec::new()
      }
    )
  )
}

/// Replace an output declaration by its input declaration dual.
///
/// Useful when an input interface must match an output one.
fn input_from_output(output: SingleDeclaration, has_array: bool) -> SingleDeclaration {
  let
    qualifier = output.ty.qualifier.map(|q| {
      TypeQualifier {
        qualifiers: q.qualifiers.into_iter().map(|qs| {
          match qs {
            TypeQualifierSpec::Storage(StorageQualifier::Out) =>
              TypeQualifierSpec::Storage(StorageQualifier::In),
            _ => qs
          }
        }).collect()
      }
    });
  let ty =
    TypeSpecifier {
      array_specifier: if has_array { Some(ArraySpecifier::Unsized) } else { None },
      .. output.ty.ty
    };

  SingleDeclaration {
    ty: FullySpecifiedType { qualifier, ty },
    .. output 
  }
}

/// Replace outputs by inputs.
fn inputs_from_outputs(outputs: &[SingleDeclaration], has_array: bool) -> Vec<SingleDeclaration> {
  outputs.into_iter().map(|sd| input_from_output(sd.clone(), has_array)).collect()
}

/// Map a StructFieldSpecifier to an ExternalDeclaration.
///
/// Typically suitable for generating an output from a struct field.
fn field_to_single_decl(field: &StructFieldSpecifier, prefix: &str) -> SingleDeclaration {
  let base_qualifier = TypeQualifierSpec::Storage(StorageQualifier::Out);
  let qualifier = match field.qualifier {
    Some(ref qual) =>
      TypeQualifier {
        qualifiers: qual.clone().qualifiers.into_iter().chain(once(base_qualifier)).collect()
      },
    None => TypeQualifier {
      qualifiers: vec![base_qualifier]
    }
  };
  let fsty = FullySpecifiedType {
    qualifier: Some(qualifier),
    ty: field.ty.clone()
  };

  SingleDeclaration {
    ty: fsty,
    name: Some(prefix.to_owned() + &field.identifiers[0].0),
    array_specifier: field.identifiers[0].1.clone(),
    initializer: None
  }
}

/// Map a struct’s fields to a Vec<ExternalDeclaration>.
///
/// Typically suitable for generating outputs from a struct fields.
fn fields_to_single_decls(fields: &[StructFieldSpecifier], prefix: &str)
                              -> Result<Vec<SingleDeclaration>, GLSLConversionError> {
  let mut outputs = Vec::new();

  for (i, field) in fields.into_iter().enumerate() {
    match field.ty.ty {
      TypeSpecifierNonArray::Struct(ref s) => {
        return Err(GLSLConversionError::OutputFieldCannotBeStruct(i + 1, s.clone()));
      }
      TypeSpecifierNonArray::TypeName(ref t) => {
        return Err(GLSLConversionError::OutputFieldCannotBeTypeName(i + 1, t.clone()));
      }
      _ => ()
    }

    if field.identifiers.len() > 1 {
      return Err(GLSLConversionError::OutputFieldCannotHaveSeveralIdentifiers(i + 1, field.clone()));
    }

    outputs.push(field_to_single_decl(&field, prefix));
  }

  Ok(outputs)
}

/// Filter out a function definition by removing its unused arguments.
fn remove_unused_args_fn(f: &FunctionDefinition) -> FunctionDefinition {
  let f = f.clone();

  FunctionDefinition {
    prototype: FunctionPrototype {
      parameters: f.prototype.parameters.into_iter().filter(is_fn_arg_named).collect(),
      .. f.prototype
    },
    .. f
  }
}

fn is_fn_arg_named(arg: &FunctionParameterDeclaration) -> bool {
  if let FunctionParameterDeclaration::Named(..) = *arg {
    true
  } else {
    false
  }
}

/// Extract the type name of a function argument. If the argument’s type is not a typename,
/// nothing is returned.
/// Get the fully specified type of a function’s argument.
fn fn_arg_as_fully_spec_ty(arg: &FunctionParameterDeclaration) -> FullySpecifiedType {
  match *arg {
    FunctionParameterDeclaration::Named(ref qualifier, FunctionParameterDeclarator {
      ref ty,
      ..
    }) => FullySpecifiedType {
      qualifier: qualifier.clone(),
      ty: ty.clone()
    },
    FunctionParameterDeclaration::Unnamed(ref qualifier, ref ty) => {
      FullySpecifiedType {
        qualifier: qualifier.clone(),
        ty: ty.clone()
      }
    }
  }
}

/// Extract the type name of a fully specified type. If the type is not a typename, nothing is
/// returned.
fn get_ty_name_from_fully_spec_ty(fst: &FullySpecifiedType) -> Result<TypeName, GLSLConversionError> {
  if let TypeSpecifierNonArray::TypeName(ref n) = fst.ty.ty {
    Ok(n.clone())
  } else {
    Err(GLSLConversionError::NotTypeName)
  }
}

/// Get the type name of the argument of a unary function. If the argument is not unary, fail
/// with the approriate error.
fn get_fn1_input_ty_name(f: &FunctionDefinition) -> Result<TypeName, GLSLConversionError> {
  let slice = f.prototype.parameters.as_slice();
  match slice {
    &[ref arg] => {
      let fst = fn_arg_as_fully_spec_ty(arg);
      get_ty_name_from_fully_spec_ty(&fst)
    }
    _ => Err(GLSLConversionError::WrongNumberOfArgs(1, slice.len()))
  }
}

/// Get the return type of a function by looking up its definition in the provided slice.
fn get_fn_ret_ty(f: &FunctionDefinition, structs: &[StructSpecifier]) -> Result<StructSpecifier, GLSLConversionError> {
  struct_from_ty_spec(&f.prototype.ty.ty, structs)
}

/// Get the struct definition associated with a type specifier.
fn struct_from_ty_spec(
  ty_spec: &TypeSpecifier,
  structs: &[StructSpecifier]
) -> Result<StructSpecifier, GLSLConversionError> {
  if let TypeSpecifierNonArray::TypeName(ref name) = ty_spec.ty {
    if let Some(ref ty) = structs.iter().find(|ref s| s.name.as_ref() == Some(name)) {
      Ok((*ty).clone())
    } else {
      Err(GLSLConversionError::ReturnTypeMustBeAStruct(ty_spec.clone()))
    }
  } else {
    Err(GLSLConversionError::ReturnTypeMustBeAStruct(ty_spec.clone()))
  }
}

/// Drop the first field of a struct.
fn drop_1st_field(s: &StructSpecifier) -> StructSpecifier {
  StructSpecifier {
    name: s.name.clone(),
    fields: s.fields.iter().skip(1).cloned().collect(),
  }
}

// Turn a &[u8] into a String.
#[inline]
fn bytes_to_string(bytes: &[u8]) -> String {
  unsafe { from_utf8_unchecked(bytes).to_owned() }
}

/// Parse a module separator and a module name.
named!(module_sep_n_name,
  do_parse!(
    char!('.') >>
    name: alphanumeric >>
    (name)
  )
);

/// Parse a module path.
///
/// foo
/// foo.bar
/// foo.bar.zoo
named!(module_path<&[u8], ModulePath>,
  do_parse!(
    // recognize at least one module name
    base: identifier >>
    // recognize the rest of the path, if any
    rest: many0!(module_sep_n_name) >>

    ({
      let mut rest = rest.clone(); // FIXME: meh?
      rest.insert(0, base.as_bytes());

      ModulePath {
        path: rest.into_iter().map(bytes_to_string).collect()
      }
    })
  )
);

/// Parse a symbol list.
///
///     ( item0, item1, item2, …)
named!(symbol_list<&[u8], Vec<ModuleSymbol>>,
  ws!(
    delimited!(char!('('),
               separated_list!(char!(','), identifier),
               char!(')')
    )
  )
);

/// Parse an import list.
named!(import_list<&[u8], ImportList>,
  ws!(do_parse!(
    tag!("use") >>
    from_module: module_path >>
    symbols: symbol_list >>
    (ImportList { module: from_module, list: symbols })
  ))
);

/// Parse a module.
named!(module<&[u8], Module>,
  ws!(do_parse!(
    imports: many0!(import_list) >>
    glsl: many0!(external_declaration) >>
    (Module { imports, glsl })
  ))
);

/// Sink a vertex shader.
fn sink_vertex_shader<F>(sink: &mut F,
                         map_vertex: &FunctionDefinition,
                         structs: &[StructSpecifier])
                         -> Result<(StructSpecifier, Vec<SingleDeclaration>), GLSLConversionError>
                         where F: Write {
  let inputs = vertex_shader_inputs(&map_vertex.prototype.parameters)?;
  let outputs = vertex_shader_outputs(&map_vertex.prototype.ty, structs)?;
  let ret_ty = get_fn_ret_ty(map_vertex, structs)?;

  sink_single_as_ext_decls(sink, inputs.iter().chain(&outputs));

  // sink the return type
  transpiler::glsl::show_struct(sink, &ret_ty);

  // sink the map_vertex function, but remove its unused arguments
  let map_vertex_reduced = remove_unused_args_fn(map_vertex);
  transpiler::glsl::show_function_definition(sink, &map_vertex_reduced);

  // void main
  let _ = sink.write_str("void main() {\n  ");

  // call the map_vertex function
  let mut assigns = String::new();
  sink_vertex_shader_output(sink, &mut assigns, &ret_ty);
  let _ = sink.write_str(" v = map_vertex(");
  sink_vertex_shader_input_args(sink, &map_vertex_reduced);
  let _ = sink.write_str(");\n");

  // assign to outputs
  let _ = sink.write_str(&assigns);

  // end of the main function
  let _ = sink.write_str("}\n\n");

  Ok((ret_ty, outputs))
}

/// Sink a vertex shader’s output.
fn sink_vertex_shader_output<F, G>(sink: &mut F, assigns: &mut G, ty: &StructSpecifier) where F: Write, G: Write {
  if let Some(ref name) = ty.name {
    let _ = sink.write_str(name);
  } else {
    panic!("cannot happen");
  }

  let _ = assigns.write_str("  gl_Position = v.chdr_Position;\n");

  // we don’t want to sink chdr_Position
  for field in &ty.fields[1..] {
    for &(ref identifier, _) in &field.identifiers {
      let _ = write!(assigns, "  chdr_v_{0} = v.{0};\n", identifier);
    }
  }
}

/// Sink the arguments of the map_vertex function.
fn sink_vertex_shader_input_args<F>(sink: &mut F, map_vertex: &FunctionDefinition) where F: Write {
  let args = &map_vertex.prototype.parameters;

  if !args.is_empty() {
    // sink the first argument upfront
    let first_arg = &args[0];

    sink_vertex_shader_input_arg(sink, 0, first_arg);

    for (i, arg) in map_vertex.prototype.parameters[1..].iter().enumerate() {
      if is_fn_arg_named(arg) {
        let _ = sink.write_str(", ");
        sink_vertex_shader_input_arg(sink, i + 1, arg);
      }
    }
  }
}

/// Sink an argument of a function.
fn sink_vertex_shader_input_arg<F>(sink: &mut F, i: usize, arg: &FunctionParameterDeclaration) where F: Write {
  match *arg {
    FunctionParameterDeclaration::Named(_, ref d) => {
      let _ = write!(sink, "chdr_{}", d.name);
    }
    FunctionParameterDeclaration::Unnamed(..) => {
      let _ = write!(sink, "chdr_unused{}", i);
    }
  }
}

/// Create a vertex’s input (`TypeQualifier`) based on the index and an already `TypeQualifier` of
/// a vertex input.
fn vertex_shader_input_qualifier(i: usize, ty_qual: &Option<TypeQualifier>) -> TypeQualifier {
  let layout_qualifier = LayoutQualifier {
    ids: vec![LayoutQualifierSpec::Identifier("location".to_owned(),
    Some(box Expr::IntConst(i as i32)))]
  };
  let base_qualifier = TypeQualifier {
    qualifiers: vec![
      TypeQualifierSpec::Layout(layout_qualifier),
      TypeQualifierSpec::Storage(StorageQualifier::In)
    ]
  };

  match *ty_qual {
    Some(ref qual) => TypeQualifier {
      qualifiers: base_qualifier.qualifiers.into_iter().chain(qual.clone().qualifiers).collect()
    },
    None => base_qualifier
  }
}

/// Extract the vertex shader inputs from a list of arguments.
fn vertex_shader_inputs<'a, I>(args: I) -> Result<Vec<SingleDeclaration>, GLSLConversionError>
    where I: IntoIterator<Item = &'a FunctionParameterDeclaration> {
  let mut inputs = Vec::new();

  for (i, arg) in args.into_iter().enumerate() {
    match *arg {
      FunctionParameterDeclaration::Named(ref ty_qual, ref decl) => {
        let qualifier = vertex_shader_input_qualifier(i, ty_qual);
        let ty = decl.ty.clone();
        let name = Some(format!("chdr_{}",  decl.name));
        let array_spec = decl.array_spec.clone();
        let sd = 
          SingleDeclaration {
            ty: FullySpecifiedType {
              qualifier: Some(qualifier),
              ty
            },
            name,
            array_specifier: array_spec,
            initializer: None
          };

        inputs.push(sd);
      }

      // unnamed arguments is not an error! it serves when the argument is not used, but we still
      // need to state how the data is stored in the buffer
      _ => ()
    }
  }

  Ok(inputs)
}

fn vertex_shader_outputs(fsty: &FullySpecifiedType, structs: &[StructSpecifier]) -> Result<Vec<SingleDeclaration>, GLSLConversionError> {
  // we refuse that the output has a main qualifier
  if fsty.qualifier.is_some() {
    return Err(GLSLConversionError::OutputHasMainQualifier);
  }

  let ty = &fsty.ty;

  // we enforce that the output must be a struct that follows a certain pattern
  match ty.ty {
    TypeSpecifierNonArray::TypeName(ref ty_name) => {
      let real_ty = structs.iter().find(|ref s| s.name.as_ref() == Some(ty_name));

      match real_ty {
        Some(ref s) => {
          check_1st_field_chdr_position(&s.fields[0])?;

          // for all other fields, we check that they are not composite type (i.e. structs); if
          // they are not, add them to the interface; otherwise, fail
          fields_to_single_decls(&s.fields[1..], "chdr_v_")
        }
        _ => Err(GLSLConversionError::ReturnTypeMustBeAStruct(ty.clone()))
      }
    }
    _ => Err(GLSLConversionError::ReturnTypeMustBeAStruct(ty.clone()))
  }
}

fn check_1st_field_chdr_position(field: &StructFieldSpecifier) -> Result<(), GLSLConversionError> {
  // the first field must be named "chdr_Position", has type vec4 and no qualifier
  if field.qualifier.is_some() ||
     field.ty.ty != TypeSpecifierNonArray::Vec4 ||
     field.identifiers.as_slice() != &[("chdr_Position".to_owned(), None)] {
    Err(GLSLConversionError::WrongOutputFirstField(field.clone()))
  } else {
    Ok(())
  }
}

/// Sink a geometry shader.
fn sink_geometry_shader<F>(
  sink: &mut F,
  concat_map_prim: &FunctionDefinition,
  structs: &[StructSpecifier],
  prev_ret_ty: &StructSpecifier,
  prev_inputs: &[SingleDeclaration],
) -> Result<(StructSpecifier, Vec<SingleDeclaration>),
             GLSLConversionError>
where F: Write {
  let fn_args = concat_map_prim.prototype.parameters.as_slice();
  let (input_ty_name, input_dim, input_layout, output_ty, output_layout) = match fn_args {
    &[ref arg0, ref arg1] => {
      let input = fn_arg_as_fully_spec_ty(arg0);
      let output = fn_arg_as_fully_spec_ty(arg1);
      let output_ty = struct_from_ty_spec(&output.ty, structs)?;

      let input_ty_name = get_ty_name_from_fully_spec_ty(&input)?;
      let (input_dim, input_layout) = guess_gs_input_prim(&input.ty.array_specifier)?;
      let output_layout = get_gs_output_layout_metadata(&output.qualifier)?;

      Ok((input_ty_name, input_dim, input_layout, output_ty, output_layout))
    }
    _ => Err(GLSLConversionError::WrongNumberOfArgs(2, fn_args.len()))
  }?;

  // ensure we use the right input type
  if Some(&input_ty_name) != prev_ret_ty.name.as_ref() {
    return Err(GLSLConversionError::UnknownInputType(input_ty_name.clone()));
  }

  // ensure the first field of the output struct is correct
  check_1st_field_chdr_position(&output_ty.fields[0])?;

  let gs_metadata_input = gs_layout_storage_external_decl(input_layout, StorageQualifier::In);
  let gs_metadata_output = gs_layout_storage_external_decl(output_layout, StorageQualifier::Out);

  transpiler::glsl::show_external_declaration(sink, &gs_metadata_input);
  transpiler::glsl::show_external_declaration(sink, &gs_metadata_output);

  let inputs = inputs_from_outputs(prev_inputs, true);
  let outputs = fields_to_single_decls(&output_ty.fields[1..], "chdr_g_")?;

  sink_single_as_ext_decls(sink, inputs.iter().chain(&outputs));

  transpiler::glsl::show_struct(sink, prev_ret_ty); // sink the previous stage’s return type
  transpiler::glsl::show_struct(sink, &output_ty); // sink the return type of this stage

  // sink the concat_map_prim function
  let concat_map_prim_fixed = unannotate_concat_map_prim(concat_map_prim.clone(), &output_ty)?;
  transpiler::glsl::show_function_definition(sink, &concat_map_prim_fixed);

  // void main
  let _ = sink.write_str("void main() {\n  ");

  // sink the vertex array input variable as "_ v = "
  let v_name = "v";
  let _ = transpiler::glsl::show_statement(sink, &gs_create_vertex_array(&prev_ret_ty, input_dim, v_name));

  // call the concat_map_prim function
  let _ = write!(sink, "  concat_map_prim({});\n", v_name);

  // end of the main function
  let _ = sink.write_str("}\n\n");

  Ok((output_ty, outputs))
}

/// Sink a fragment shader.
fn sink_fragment_shader<F>(sink: &mut F,
                           map_frag_data: &FunctionDefinition,
                           structs: &[StructSpecifier],
                           prev_ret_ty: &StructSpecifier,
                           prev_inputs: &[SingleDeclaration],
                           ) -> Result<(StructSpecifier, Vec<SingleDeclaration>), GLSLConversionError>
                           where F: Write {
  let input_ty_name = get_fn1_input_ty_name(map_frag_data)?;

  // ensure we use the right input type
  if Some(&input_ty_name) != prev_ret_ty.name.as_ref() {
    return Err(GLSLConversionError::UnknownInputType(input_ty_name.clone()));
  }

  let inputs = inputs_from_outputs(prev_inputs, false);
  let ret_ty = get_fn_ret_ty(map_frag_data, structs)?;
  let outputs = fields_to_single_decls(&ret_ty.fields, "chdr_f_")?;

  sink_single_as_ext_decls(sink, inputs.iter().chain(&outputs));

  // we don’t sink the return type of the fragment shader if it only has one field
  if prev_ret_ty.fields.len() > 1 {
    // we remove the first field of that struct since it’s chdr_Position
    let dropped_ret_ty = drop_1st_field(&prev_ret_ty);
    transpiler::glsl::show_struct(sink, &dropped_ret_ty); // sink the previous stage’s return type
  }

  transpiler::glsl::show_struct(sink, &ret_ty); // sink the return type of this stage

  // sink the map_frag_data function
  let map_frag_data_reduced = remove_unused_args_fn(map_frag_data);
  transpiler::glsl::show_function_definition(sink, &map_frag_data_reduced);

  // void main
  let _ = sink.write_str("void main() {\n");

  if inputs.len() > 0 {
    // if we have at least one input, we must construct the input type, bindi it to a local i
    // varible and pass it to map_frag_data
    let _ = write!(sink, "{0} i = {0}(", prev_ret_ty.name.as_ref().unwrap());
    let _ = sink.write_str(inputs[0].name.as_ref().unwrap());

    for input in &inputs[1..] {
      let _ = write!(sink, ", {}", input.name.as_ref().unwrap());
    }

    let _ = sink.write_str(");\n");
    let _ = write!(sink, "  {} o = {}(i);\n", ret_ty.name.as_ref().unwrap(), "map_frag_data");
  } else {
    // no argument, we don’t need to build the type; just direct call to map_frag_data
    let _ = write!(sink, "  {} o = {}();\n", ret_ty.name.as_ref().unwrap(), "map_frag_data");
  }

  for (output, ret_ty_field) in outputs.iter().zip(&ret_ty.fields) {
    let _ = write!(sink, "  {} = o.{};\n", output.name.as_ref().unwrap(), ret_ty_field.identifiers[0].0);
  }

  // end of the main function
  let _ = sink.write_str("}\n\n");

  Ok((ret_ty, outputs))
}

fn filter_out_special_functions<'a, I>(
  functions: I
) -> impl Iterator<Item = &'a FunctionDefinition>
where I: Iterator<Item = &'a FunctionDefinition>
{
  functions.filter(|f| {
    let n: &str = &f.prototype.name;
    n != "map_vertex" && n != "concat_map_prim" && n != "map_frag_data"
  })
}

fn guess_gs_input_prim(array_specifier: &Option<ArraySpecifier>) -> Result<(usize, LayoutQualifier), GLSLConversionError> {
  match *array_specifier {
    Some(ArraySpecifier::ExplicitlySized(box Expr::IntConst(size))) => {
      match size {
        1 => Ok((1, LayoutQualifier { ids: vec![LayoutQualifierSpec::Identifier("points".to_owned(), None)] })),
        2 => Ok((2, LayoutQualifier { ids: vec![LayoutQualifierSpec::Identifier("lines".to_owned(), None)] })),
        3 => Ok((3, LayoutQualifier { ids: vec![LayoutQualifierSpec::Identifier("triangles".to_owned(), None)] })),
        4 => Ok((4, LayoutQualifier { ids: vec![LayoutQualifierSpec::Identifier("lines_adjacency".to_owned(), None)] })),
        6 => Ok((6, LayoutQualifier { ids: vec![LayoutQualifierSpec::Identifier("triangles_adjacency".to_owned(), None)] })),
        _ => Err(GLSLConversionError::WrongGeometryInputDim(size as usize))
      }
    },
    _ => Err(GLSLConversionError::WrongGeometryInput)
  }
}

fn gs_layout_storage_external_decl(
  layout: LayoutQualifier,
  storage: StorageQualifier
) -> ExternalDeclaration {
  let ty_qual =
    TypeQualifier {
      qualifiers:
        vec![
          TypeQualifierSpec::Layout(layout),
          TypeQualifierSpec::Storage(storage)
        ]
    };

  ExternalDeclaration::Declaration(Declaration::Global(ty_qual, Vec::new()))
}

fn get_gs_output_layout_metadata(qual: &Option<TypeQualifier>) -> Result<LayoutQualifier, GLSLConversionError> {
  let qual = qual.as_ref().ok_or(GLSLConversionError::WrongGeometryOutputLayout(qual.clone()))?;

  match qual.qualifiers.as_slice() {
    &[TypeQualifierSpec::Layout(ref layout_qual), TypeQualifierSpec::Storage(StorageQualifier::Out)] => {
      match layout_qual.ids.as_slice() {
        &[LayoutQualifierSpec::Identifier(ref output_prim_str, None),
          LayoutQualifierSpec::Identifier(ref max_vertices_str, Some(box Expr::IntConst(_)))] if max_vertices_str == "max_vertices" => {
          if check_gs_output_prim(output_prim_str) {
            Ok(layout_qual.clone())
          } else {
            Err(GLSLConversionError::WrongGeometryOutputLayout(Some(qual.clone())))
          }
        },
        _ => Err(GLSLConversionError::WrongGeometryOutputLayout(Some(qual.clone())))
      }
    },
    _ => Err(GLSLConversionError::WrongGeometryOutputLayout(Some(qual.clone())))
  }
}

fn check_gs_output_prim(s: &str) -> bool {
  match s {
    "points" | "line_strip" | "triangle_strip" => true,
    _ => false
  }
}

/// Fix the concat_map_prim function for geometry shaders. This function will remove all the
/// GLSL that is normally illegal (only hints for us) and fix the EDSL one.
///
/// The first argument is a valid GLSL one – i.e. the input. The second one is used as hint
/// only and must completely be removed.
///
/// This function will also replace any call to the `yield_vertex` and `yield_primitive` by the
/// correct GLSL counterpart.
fn unannotate_concat_map_prim(f: FunctionDefinition, out_ty: &StructSpecifier) -> Result<FunctionDefinition, GLSLConversionError> {
  let st = f.statement.statement_list.iter().map(|st| unyield_stmt(st, out_ty)).collect::<Result<_, _>>()?;

  Ok(FunctionDefinition {
    prototype: FunctionPrototype {
      parameters: f.prototype.parameters.into_iter().take(1).collect(),
      .. f.prototype
    },
    statement: CompoundStatement {
      statement_list: st
    }
  })
}

/// Recursively remove any `yield_*` annotations from a statement and replace them with correct GLSL
/// code.
fn unyield_stmt(st: &Statement, out_ty: &StructSpecifier) -> Result<Statement, GLSLConversionError> {
  match *st {
    Statement::Simple(box ref sst) => {
      match *sst {
        SimpleStatement::Expression(
          Some(
            Expr::FunCall(FunIdentifier::Identifier(ref fni), ref args))) => {
              match fni.as_str() {
                "yield_vertex" => yield_vertex(&args, out_ty),
                "yield_primitive" => Ok(yield_primitive()),
                _ => Ok(st.clone())
              }
            }

        SimpleStatement::Selection(ref sst) => {
          let st =
            Statement::Simple(
              box SimpleStatement::Selection(
                SelectionStatement {
                  rest:
                    match sst.rest {
                      SelectionRestStatement::Statement(box ref st) =>
                        SelectionRestStatement::Statement(box unyield_stmt(&st, out_ty)?),

                      SelectionRestStatement::Else(box ref ist, box ref est) =>
                        SelectionRestStatement::Else(box unyield_stmt(&ist, out_ty)?, box unyield_stmt(&est, out_ty)?)
                    },
                  .. sst.clone()
                }
              )
            );

          Ok(st)
        }

        SimpleStatement::Switch(ref sst) => {
          let st =
            Statement::Simple(
              box SimpleStatement::Switch(
                SwitchStatement {
                  head: sst.head.clone(),
                  body: sst.body.iter().map(|s| unyield_stmt(&s, out_ty)).collect::<Result<_, _>>()?
                }
              )
            );

          Ok(st)
        }

        SimpleStatement::Iteration(ref ist) => {
          match *ist {
            IterationStatement::While(ref cond, box ref s) => {
              let st =
                Statement::Simple(
                  box SimpleStatement::Iteration(
                    IterationStatement::While(cond.clone(), box unyield_stmt(&s, out_ty)?)
                  )
                );

              Ok(st)
            }

            IterationStatement::DoWhile(box ref s, ref x) => {
              let st =
                Statement::Simple(
                  box SimpleStatement::Iteration(
                    IterationStatement::DoWhile(box unyield_stmt(&s, out_ty)?, x.clone())
                  )
                );

              Ok(st)
            }

            IterationStatement::For(ref i, ref cond, box ref s) => {
              let st =
                Statement::Simple(
                  box SimpleStatement::Iteration(
                    IterationStatement::For(i.clone(), cond.clone(), box unyield_stmt(&s, out_ty)?)
                  )
                );

              Ok(st)
            }
          }
        }

        _ => Ok(st.clone())
      }
    }

    Statement::Compound(box CompoundStatement { statement_list: ref stmts }) => {
      let st =
        Statement::Compound(
          box CompoundStatement {
            statement_list: stmts.iter().map(|s| unyield_stmt(s, out_ty)).collect::<Result<_, _>>()?
          }
        );

      Ok(st)
    }
  }
}

/// Turn a `yield_vertex` function into a block of GLSL assigning outputs and emitting a vertex.
fn yield_vertex(args: &[Expr], out_ty: &StructSpecifier) -> Result<Statement, GLSLConversionError> {
  match args {
    &[ref arg] => {
      // bind the argument to a variable so that we can re-use it if it’s a literal
      let binding = Statement::Simple(
        box SimpleStatement::Declaration(
          Declaration::InitDeclaratorList(
            InitDeclaratorList {
              head: SingleDeclaration {
                ty: FullySpecifiedType {
                  qualifier: None,
                  ty: TypeSpecifier {
                    ty: TypeSpecifierNonArray::TypeName(out_ty.name.as_ref().unwrap().clone()),
                    array_specifier: None
                  },
                },
                name: Some("chdr_v".to_owned()), // special name to prevent from shadowing
                array_specifier: None,
                initializer: Some(Initializer::Simple(box arg.clone()))
              },
              tail: Vec::new()
            }
          )
        )
      );

      // variable to refer the binding
      let bvar = box Expr::Variable("chdr_v".to_owned());

      // assign gl_Position
      let assign_gl_position =
        Statement::Simple(
          box SimpleStatement::Expression(
            Some(Expr::Assignment(
              box Expr::Variable("gl_Position".to_owned()),
              AssignmentOp::Equal,
              box Expr::Dot(bvar.clone(), "chdr_Position".to_owned())
            ))
          )
        );

      // iterate over the fields of the vertex, but don’t include the first one, which is always
      // chdr_Position
      let assigns = out_ty.fields.iter().skip(1).flat_map(|field| field.identifiers.iter().map(|&(ref field_name, _)| {
        Statement::Simple(
          box SimpleStatement::Expression(
            Some(Expr::Assignment(
              box Expr::Variable("chdr_g_".to_owned() + field_name),
              AssignmentOp::Equal,
              box Expr::Dot(bvar.clone(), field_name.to_owned())
            ))
          )
        )
      }));

      let emit =
        Statement::Simple(
          box SimpleStatement::Expression(
            Some(Expr::FunCall(FunIdentifier::Identifier("EmitVertex".to_owned()),
                                       Vec::new()))
          )
        );

      // create the final block of GLSL code
      let block =
        CompoundStatement {
          statement_list:
            once(binding)
            .chain(once(assign_gl_position))
            .chain(assigns)
            .chain(once(emit))
            .collect()
        };
      Ok(Statement::Compound(box block))
    },
    _ => Err(GLSLConversionError::WrongNumberOfArgs(1, args.len()))
  }
}

fn yield_primitive() -> Statement {
  Statement::Simple(
    box SimpleStatement::Expression(
      Some(Expr::FunCall(
          FunIdentifier::Identifier("EndPrimitive".to_owned()),
          Vec::new())
      )
    )
  )
}

fn gs_create_vertex_array(v_ty: &StructSpecifier, dim: usize, binding_name: &str) -> Statement {
  let v_ty_name = v_ty.name.as_ref().unwrap();

  // rhs part of the assignment
  let fun_id =
    FunIdentifier::Expr(
      box Expr::Bracket(box Expr::Variable(v_ty_name.to_owned()),
                                ArraySpecifier::Unsized
      )
    );
  let fun_args =
    (0..dim).into_iter().map(|i| {
      // arguments passed in the vertex constructor
      let v_ctor_args =
        v_ty.fields.iter().flat_map(|field| field.identifiers.iter().map(|&(ref field_name, _)| {
          Expr::Bracket(box Expr::Variable(format!("chdr_v_{}", field_name)),
                                ArraySpecifier::ExplicitlySized(
                                  box Expr::IntConst(i as i32)
                                )
          )
        })).collect();

      // invoke the vertex constructor
      Expr::FunCall(FunIdentifier::Identifier(v_ty_name.to_owned()), v_ctor_args)
    }).collect();
  let rhs = Expr::FunCall(fun_id, fun_args);

  // type specifier of the resulting value
  let res_ty = TypeSpecifier {
    ty: TypeSpecifierNonArray::TypeName(v_ty_name.to_owned()),
    array_specifier: Some(ArraySpecifier::ExplicitlySized(box Expr::IntConst(dim as i32)))
  };

  // return the assignment as a statement
  Statement::Simple(
    box SimpleStatement::Declaration(
      Declaration::InitDeclaratorList(
        InitDeclaratorList {
          head:
            SingleDeclaration {
              ty:
                FullySpecifiedType {
                  qualifier: None,
                  ty: res_ty,
                },
              name: Some(binding_name.to_owned()),
              array_specifier: None,
              initializer: Some(Initializer::Simple(box rhs))
            },
          tail: Vec::new()
        }
      )
    )
  )
}

#[cfg(test)]
mod tests {
  use nom::IResult;
  use super::*;

  #[test]
  fn parse_module_sep_n_name() {
    assert_eq!(module_sep_n_name(&b".foo"[..]), IResult::Done(&b""[..], &b"foo"[..]));
    assert_eq!(module_sep_n_name(&b".foo.bar"[..]), IResult::Done(&b".bar"[..], &b"foo"[..]));
  }
  
  #[test]
  fn parse_module_path_simple() {
    assert_eq!(module_path(&b"foo"[..]), IResult::Done(&b""[..], ModulePath { path: vec!["foo".into()] }));
    assert_eq!(module_path(&b"  \n\tfoo \n"[..]), IResult::Done(&b""[..], ModulePath { path: vec!["foo".into()] }));
  }
  
  #[test]
  fn parse_module_path_several() {
    assert_eq!(module_path(&b"foo.bar.zoo"[..]), IResult::Done(&b""[..], ModulePath { path: vec!["foo".into(), "bar".into(), "zoo".into()] }));
  }
  
  #[test]
  fn parse_symbol_list() {
    let foo = "foo".to_owned();
    let bar = "bar".to_owned();
    let zoo = "zoo".to_owned();
    let list = vec![foo, bar, zoo];
  
    assert_eq!(symbol_list(&b"(foo,bar,zoo)"[..]), IResult::Done(&b""[..], list.clone()));
    assert_eq!(symbol_list(&b" ( foo,bar,zoo  ) "[..]), IResult::Done(&b""[..], list.clone()));
    assert_eq!(symbol_list(&b"( foo, bar ,   zoo  )"[..]), IResult::Done(&b""[..], list.clone()));
  }
  
  #[test]
  fn parse_import_list() {
    let foo = "foo".to_owned();
    let bar = "bar".to_owned();
    let zoo_woo = ModulePath { path: vec!["zoo".into(), "woo".into()] };
    let expected = ImportList { module: zoo_woo, list: vec![foo, bar] };
  
    assert_eq!(import_list(&b"use zoo.woo (foo, bar)"[..]), IResult::Done(&b""[..], expected.clone()));
    assert_eq!(import_list(&b" use    zoo.woo    (   foo  ,   bar  )"[..]), IResult::Done(&b""[..], expected.clone()));
    assert_eq!(import_list(&b"use zoo.woo (foo,\nbar)"[..]), IResult::Done(&b""[..], expected.clone()));
  }
}


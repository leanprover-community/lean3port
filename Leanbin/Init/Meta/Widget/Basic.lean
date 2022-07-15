/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import Leanbin.Init.Function
import Leanbin.Init.Data.Option.Basic
import Leanbin.Init.Util
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.MkDecEqInstance
import Leanbin.Init.Meta.Json

/-! A component is a piece of UI which may contain internal state. Use component.mk to build new components.

## Using widgets.

To make a widget, you need to make a custom executor object and then instead of calling `save_info_thunk` you call `save_widget`.

Additionally, you will need a compatible build of the vscode extension or web app to use widgets in vscode.

## How it works:

The design is inspired by React.
If you are familiar with using React or Elm or a similar functional UI framework then that's helpful for this.
The [React article on reconciliation](https://reactjs.org/docs/reconciliation.html) might be helpful.

One can imagine making a UI for a particular object as just being a function `f : α → UI` where `UI` is some inductive datatype for buttons, textboxes, lists and so on.
The process of evaluating `f` is called __rendering__.
So for example `α` could be `tactic_state` and the function renders a goal view.

## HTML

For our purposes, `UI` is an HTML tree and is written `html α : Type`. I'm going to assume some familiarity with HTML for the purposes of this document.
An HTML tree is composed of elements and strings.
Each element has a tag such as "div", "span", "article" and so on and a set of attributes and child html.
Use the helper function `h : string → list (attr α) → list (html α) → html α` to build new pieces of `html`. So for example:

```lean
h "ul" [] [
     h "li" [] ["this is list item 1"],
     h "li" [style [("color", "blue")]] ["this is list item 2"],
     h "hr" [] [],
     h "li" [] [
          h "span" [] ["there is a button here"],
          h "button" [on_click (λ _, 3)] ["click me!"]
     ]
]
```
Has the type `html nat`.
The `nat` type is called the __action__ and whenever the user interacts with the UI, the html will emit an object of type `nat`.
So for example if the user clicks the button above, the html will 'emit' `3`.
The above example is compiled to the following piece of html:

```html
<ul>
  <li>this is list item 1</li>
  <li style="{ color: blue; }">this is list item 2</li>
  <hr/>
  <li>
     <span>There is a button here</span>
     <button onClick="[handler]">click me!</button>
  </li>
</ul>
```

## Components

In order for the UI to react to events, you need to be able to take these actions α and alter some state.
To do this we use __components__. `component` takes two type arguments: `π` and `α`. `α` is called the 'action' and `π` are the 'props'.
The props can be thought of as a kind of wrapped function domain for `component`. So given `C : component nat α`, one can turn this into html with
`html.of_component 4 C : html α`.

The base constructor for a component is `pure`:
```lean
meta def Hello : component string α := component.pure (λ s, ["hello, ", s, ", good day!"])

#html Hello "lean" -- renders "hello, lean, good day!"
```
So here a pure component is just a simple function `π → list (html α)`.
However, one can augment components with __hooks__.
The hooks available for compoenents are listed in the inductive definition for component.

Here we will just look at the `with_state` hook, which can be used to build components with inner state.

```
meta inductive my_action
| increment
| decrement
open my_action

meta def Counter : component unit α :=
component.with_state
     my_action          -- the action of the inner component
     int                -- the state
     (λ _, 0)           -- initialise the state
     (λ _ _ s, s)       -- update the state if the props change
     (λ _ s a,          -- update the state if an action was received
          match a with
          | increment := (s + 1, none) -- replace `none` with `some _` to emit an action
          | decrement := (s - 1, none)
          end
     )
$ component.pure (λ ⟨state, ⟨⟩⟩, [
     button "+" (λ _, increment),
     to_string state,
     button "-" (λ _, decrement)
  ])

#html Counter ()
```

You can add many hooks to a component.

- `filter_map_action` lets you filter or map actions that are emmitted by the component
- `map_props` lets you map the props.
- `with_should_update` will not re-render the child component if the given test returns false. This can be useful for efficiency.
- `with_state` discussed above.`
- `with_mouse` subscribes the component to the mouse state, for example whether or not the mouse is over the component. See the `tests/lean/widget/widget_mouse.lean` test for an example.

Given an active document, Lean (in server mode) maintains a set of __widgets__ for the document.
A widget is a component `c`, some `p : Props` and an internal state-manager which manages the states
of the component and subcomponents and also handles the routing of events from the UI.

## Reconciliation

If a parent component's state changes, this can cause child components to change position or to appear and dissappear.
However we want to preserve the state of these child components where we can.
The UI system will try to match up these child components through a process called __reconciliation__.

Reconciliation will make sure that the states are carried over correctly and will also not rerender subcomponents if they haven't changed their props or state.
To compute whether two components are the same, the system will perform a hash on their VM objects.
Not all VM objects can be hashed, so it's important to make sure that any items that you expect to change over the lifetime of the component are fed through the 'Props' argument.
This is why we need the props argument on `component`.
The reconciliation engine uses the `props_eq` predicate passed to the component constructor to determine whether the props have changed and hence whether the component should be re-rendered.

## Keys

If you have some list of components and the list changes according to some state, it is important to add keys to the components so
that if two components change order in the list their states are preserved.
If you don't provide keys or there are duplicate keys then you may get some strange behaviour in both the Lean widget engine and react.

It is possible to use incorrect HTML tags and attributes, there is (currently) no type checking that the result is a valid piece of HTML.
So for example, the client widget system will error if you add a `text_change_event` attribute to anything other than an element tagged with `input`.

## Styles with Tachyons

The widget system assumes that a stylesheet called 'tachyons' is present.
You can find documentation for this stylesheet at [Tachyons.io](http://tachyons.io/).
Tachyons was chosen because it is very terse and allows arbitrary styling without using inline styles and without needing to dynamically load a stylesheet.

## Further work (up for grabs!)

- Add type checking for html.
- Better error handling when the html tree is malformed.
- Better error handling when keys are malformed.
- Add a 'with_task' which lets long-running operations (eg running `simp`) not block the UI update.
- Timers, animation (ambitious).
- More event handlers
- Drag and drop support.
- The current perf bottleneck is sending the full UI across to the server for every update.
  Instead, it should be possible to send a smaller [JSON Patch](http://jsonpatch.com).
  Which is already supported by `json.hpp` and javascript ecosystem.

-/


namespace Widget

inductive MouseEventKind
  | on_click
  | on_mouse_enter
  | on_mouse_leave

/-- An effect is some change that the widget makes outside of its own state.
Usually, giving instructions to the editor to perform some task.
- `insert_text_relative` will insert at a line relative to the position of the widget.
- `insert_text_absolute` will insert text at the precise position given.
- `reveal_position` will move the editor to view the given position.
- `highlight_position` will add a text highlight to the given position.
- `clear_highlighting` will remove all highlights created with `highlight_position`.
- `copy_text` will copy the given text to the clipboard.
- `custom` can be used to pass custom effects to the client without having to recompile Lean.
-/
unsafe inductive effect : Type
  | insert_text_absolute (file_name : Option Stringₓ) (p : Pos) (text : Stringₓ)
  | insert_text_relative (relative_line : Int) (text : Stringₓ)
  | reveal_position (file_name : Option Stringₓ) (p : Pos)
  | highlight_position (file_name : Option Stringₓ) (p : Pos)
  | clear_highlighting
  | copy_text (text : Stringₓ)
  | custom (key : Stringₓ) (value : Stringₓ)

unsafe def effects :=
  List effect

mutual
  unsafe inductive component : Type → Type → Type
    | pure {Props Action : Type} (view : Props → List (html Action)) : component Props Action
    | filter_map_action {Props InnerAction OuterAction} (action_map : Props → InnerAction → Option OuterAction) :
      component Props InnerAction → component Props OuterAction
    | map_props {Props1 Props2 Action} (map : Props2 → Props1) : component Props1 Action → component Props2 Action
    | with_should_update {Props Action : Type} (should_update : ∀ old new : Props, Bool) :
      component Props Action → component Props Action
    | with_state {Props Action : Type} (InnerAction State : Type) (init : Props → State)
      (props_changed : Props → Props → State → State) (update : Props → State → InnerAction → State × Option Action) :
      component (State × Props) InnerAction → component Props Action
    | with_effects {Props Action : Type} (emit : Props → Action → effects) :
      component Props Action → component Props Action
  unsafe inductive html : Type → Type
    | element {α : Type} (tag : Stringₓ) (attrs : List (attr α)) (children : List (html α)) : html α
    | of_string {α : Type} : Stringₓ → html α
    | of_component {α : Type} {Props : Type} : Props → component Props α → html α
  unsafe inductive attr : Type → Type
    | val {α : Type} (name : Stringₓ) (value : json) : attr α
    | mouse_event {α : Type} (kind : MouseEventKind) (handler : Unit → α) : attr α
    | style {α : Type} : List (Stringₓ × Stringₓ) → attr α
    | tooltip {α : Type} : html α → attr α
    | text_change_event {α : Type} (handler : Stringₓ → α) : attr α
end

variable {α β : Type} {π : Type}

namespace Component

unsafe def map_action (f : α → β) : component π α → component π β
  | c => filter_map_action (fun p a => some <| f a) c

/-- Returns a component that will never trigger an action. -/
unsafe def ignore_action : component π α → component π β
  | c => component.filter_map_action (fun p a => none) c

unsafe def ignore_props : component Unit α → component π α
  | c => (with_should_update fun a b => false) <| component.map_props (fun p => ()) c

unsafe instance : Coe (component π Empty) (component π α) :=
  ⟨component.filter_map_action fun p x => none⟩

unsafe instance : CoeFun (component π α) fun c => π → html α :=
  ⟨fun c p => html.of_component p c⟩

unsafe def stateful {π α : Type} (β σ : Type) (init : π → Option σ → σ) (update : π → σ → β → σ × Option α)
    (view : π → σ → List (html β)) : component π α :=
  with_state β σ (fun p => init p none) (fun _ p s => init p <| some s) update (component.pure fun ⟨s, p⟩ => view p s)

unsafe def stateless {π α : Type} [DecidableEq π] (view : π → List (html α)) : component π α :=
  (component.with_should_update fun p1 p2 => p1 ≠ p2) <| component.pure view

/-- Causes the component to only update on a props change when `test old_props new_props` yields `ff`. -/
unsafe def with_props_eq (test : π → π → Bool) : component π α → component π α
  | c => component.with_should_update (fun x y => bnot <| test x y) c

end Component

mutual
  unsafe def attr.map_action (f : α → β) : attr α → attr β
    | attr.val k v => attr.val k v
    | attr.style s => attr.style s
    | attr.tooltip h => attr.tooltip <| html.map_action h
    | attr.mouse_event k a => attr.mouse_event k (f ∘ a)
    | attr.text_change_event a => attr.text_change_event (f ∘ a)
  unsafe def html.map_action (f : α → β) : html α → html β
    | html.element t a c => html.element t (List.map attr.map_action a) (List.map html.map_action c)
    | html.of_string s => html.of_string s
    | html.of_component p c => html.of_component p <| component.map_action f c
end

unsafe instance attr.is_functor : Functor attr where map := @attr.map_action

unsafe instance html.is_functor : Functor html where map := fun _ _ => html.map_action

namespace Html

/-- See Note [use has_coe_t]. -/
unsafe instance to_string_coe [HasToString β] : CoeTₓ β (html α) :=
  ⟨html.of_string ∘ toString⟩

unsafe instance : HasEmptyc (html α) :=
  ⟨of_string ""⟩

unsafe instance list_coe : Coe (html α) (List (html α)) :=
  ⟨fun x => [x]⟩

end Html

unsafe def as_element : html α → Option (Stringₓ × List (attr α) × List (html α))
  | html.element t a c => some ⟨t, a, c⟩
  | _ => none

unsafe def key [HasToString β] : β → attr α
  | s => attr.val "key" <| toString s

unsafe def className : Stringₓ → attr α
  | s => attr.val "className" <| s

unsafe def on_click : (Unit → α) → attr α
  | a => attr.mouse_event MouseEventKind.on_click a

unsafe def on_mouse_enter : (Unit → α) → attr α
  | a => attr.mouse_event MouseEventKind.on_mouse_enter a

unsafe def on_mouse_leave : (Unit → α) → attr α
  | a => attr.mouse_event MouseEventKind.on_mouse_leave a

/-- Alias for `html.element`. -/
unsafe def h : Stringₓ → List (attr α) → List (html α) → html α :=
  html.element

/-- Alias for className. -/
unsafe def cn : Stringₓ → attr α :=
  className

unsafe def button : Stringₓ → Thunkₓ α → html α
  | s, t => h "button" [on_click t] [s]

unsafe def textbox : Stringₓ → (Stringₓ → α) → html α
  | s, t => h "input" [attr.val "type" "text", attr.val "value" s, attr.text_change_event t] []

unsafe structure select_item (α : Type) where
  result : α
  key : Stringₓ
  view : List (html α)

/-- Choose from a dropdown selection list. -/
unsafe def select {α} [DecidableEq α] : List (select_item α) → α → html α
  | items, value =>
    let k :=
      match List.filterₓ (fun i => select_item.result i = value) items with
      | [] => ""
      | h :: _ => select_item.key h
    h "select"
        [attr.val "value" k, attr.val "key" k,
          attr.text_change_event fun k =>
            match items.filter fun i => select_item.key i = k with
            | [] => undefined
            | h :: _ => h.result] <|
      items.map fun i => h "option" [attr.val "value" i.key] <| select_item.view i

/-- If the html is not an of_element it will wrap it in a div. -/
unsafe def with_attrs : List (attr α) → html α → html α
  | a, x =>
    match as_element x with
    | some ⟨t, as, c⟩ => html.element t (a ++ as) c
    | none => html.element "div" a [x]

/-- If the html is not an of_element it will wrap it in a div. -/
unsafe def with_attr : attr α → html α → html α
  | a, x => with_attrs [a] x

unsafe def with_style : Stringₓ → Stringₓ → html α → html α
  | k, v, h => with_attr (attr.style [(k, v)]) h

unsafe def with_cn : Stringₓ → html α → html α
  | s, h => with_attr (className s) h

unsafe def with_key {β} [HasToString β] : β → html α → html α
  | s, h => with_attr (key s) h

unsafe def effect.insert_text : Stringₓ → effect :=
  effect.insert_text_relative 0

end Widget

namespace Tactic

/-- Same as `tactic.save_info_thunk` except saves a widget to be displayed by a compatible infoviewer. -/
unsafe axiom save_widget : Pos → widget.component tactic_state Empty → tactic Unit

/-- Outputs a widget trace position at the given position. -/
unsafe axiom trace_widget_at (p : Pos) (w : widget.component tactic_state Empty) (text := "(widget)") : tactic Unit

/-- Outputs a widget trace position at the current default trace position. -/
unsafe def trace_widget (w : widget.component tactic_state Empty) (text := "(widget)") : tactic Unit := do
  let p ← get_trace_msg_pos
  trace_widget_at p w text

end Tactic


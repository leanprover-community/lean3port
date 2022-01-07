prelude
import Leanbin.Init.Logic

/-- A task is a promise to produce a value later. They perform the same role as promises in JavaScript. -/
unsafe axiom task.{u} : Type u → Type u

namespace Task

unsafe axiom get.{u} {α : Type u} (t : task α) : α

protected unsafe axiom pure.{u} {α : Type u} (t : α) : task α

protected unsafe axiom map.{u, v} {α : Type u} {β : Type v} (f : α → β) (t : task α) : task β

protected unsafe axiom flatten.{u} {α : Type u} : task (task α) → task α

protected unsafe def bind.{u, v} {α : Type u} {β : Type v} (t : task α) (f : α → task β) : task β :=
  task.flatten (task.map f t)

@[inline]
unsafe def delay.{u} {α : Type u} (f : Unit → α) : task α :=
  task.map f (task.pure ())

end Task


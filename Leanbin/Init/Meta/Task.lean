namespace Task

protected def flatten (t : Task (Task α)) : Task α :=
  t.bind id

def delay (f : Unit → α) : Task α :=
  Task.spawn f

end Task


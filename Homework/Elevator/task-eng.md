## Simple elevator

We're going to model a simple elevator and also prove some properties relating to it.

We'll explicitly avoid mentioning floors in order to keep the task simple

There's a skeleton for the tasks in this same directory with the necessary imports for solving them

### `State`
```agda
data State : Set where
```

Define a data type to be used for expressing the state of an elevator - `State`.
We want our elevator to support the following states:
  1. idle - the elevator is not moving an is not doing anything overall
  2. doors are closing - the elevator is preparing to begin travel to a certain floor, which is interruptible
  3. moving to - the elevator has finalised that it will travel to certain floor and is busy doing so

#### `eqState : State -> State -> Two`
We'll need to later distinguish between two `State`s.

For this purpose, we'll implement `eqState`, being a boolean function returning whether its arguments are equal.


### `Action`
```agda
data Action : State -> Set where
```

Define a data type which expresses the possible events that our elevator will need to handle - `Action`.
  1. "call to" - someone has called the elevator to a floor which is different from its current floor
  2. "go to" - someone has pressed a button from inside the elevator with the goal of going to a certain floor, different from the current one
  3. "open doors" - someone has asked that the doors open while they were in the process of being closed, interrupting its current command
  4. "doors closed" - while the elevator was in the process of closing its doors, they managed to successfully close
  5. "arrived at" - the elevator has arrived at a certain floor, while it was in the process of travelling to that floor

You'll have `Action` be indexed by `State`, so that we can use the index to guarantee these properties:
  1. The elevator can only be "called to" and made to "go to" while it is idle.
  2. We allow "open doors" only while the elevator is in the process of closing its doors.
  3. We allow handling the "doors closed" event only when they are in the process of being closed.
  4. We allow handling the "arrived at" event only when the elevator is travelling.

### `transition`
```agda
transition : (s : State) -> Action s -> State
```

Implement the function which transitions an elevator from its current state to a new state, based on an action that is valid for its current state.

We want `transition` to have some additional properties, which you'll have the task of formulating and proving.
In order to express these properties, you can use `eqState`, as well as the `Is` type, found in `Lib.Two`.

#### The elevators travel is not interruptible
While we're in "moving to", `transition` only allows the elevator to reach its destination and become idle.

#### While idle, the elevator can only begin closing its doors
While the elevator is in a state of idleness, `transition` will only allow it to start closing its doors.

#### While the doors are being closed, we can only transition to idleness or to moving to

#### The progress property
Whatever the state and whatever the action, `transition` will always change the state.

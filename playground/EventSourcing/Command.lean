abbrev TenantId := String
abbrev UserSub := String
abbrev Decision := String -- This is just a placeholder
abbrev TenantDecider (α : Type u) := α -> TenantId -> UserSub -> Decision
abbrev NonTenantDecider (α : Type u) (requiresAuth: Bool) := α -> (if requiresAuth then UserSub else Option UserSub) -> Decision
inductive Access where
  | Tenant (roles: List String)
  | RequiresAuth (roles: List String)
  | Anyone

abbrev Decider (α : Type u) (access : Access) :=
  match access with
  | Access.Tenant _ => TenantDecider α
  | Access.RequiresAuth _ => NonTenantDecider α true
  | Access.Anyone => NonTenantDecider α false

structure Command (α : Type u) (access : Access) where
  decider : Decider α access
  name : String

class HasEntityId (α : Type u) where
  tryGetEntityId : α -> Option String

class HasUniqueName (α : Type u) where
  uniqueName : String

class CommandDefinition (α : Type u) extends (HasEntityId α), (HasUniqueName α)

def command (α : Type u)
    [HasEntityId α]
    [HasUniqueName α]
    (access : Access)
    (decider : Decider α access)
    : Command α access :=
  { decider
    name := HasUniqueName.uniqueName α }

structure ReserveStock where
  productId: String
  amount: Nat

instance : CommandDefinition ReserveStock where
  tryGetEntityId := (·.productId)
  uniqueName := "ReserveStock"

#check
  command
    ReserveStock
    (Access.RequiresAuth ["store-clerk"])
    (λ _ _ => "some decision")

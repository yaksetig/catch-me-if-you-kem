import ChannelEstablishment.CryptoInterfaces

/-!
# ChannelEstablishment.Registry

The global public registry mapping user identities to public keys, and the
key-ownership environment linking secret keys to registered public keys.
-/

namespace ChannelEstablishment

open ProtocolTypes

variable [T : ProtocolTypes]

/-- The public registry: a partial map from users to public keys, with the
invariant that any successful lookup corresponds to a registered user. -/
structure Registry where
  /-- Look up a user's public key. -/
  lookup : UserId → Option PublicKey
  /-- Predicate: the user is registered. -/
  registered : UserId → Prop
  /-- Any successful lookup is of a registered user. -/
  lookup_registered :
    ∀ u pk, lookup u = some pk → registered u

/-- The environment invariant tying secret-key ownership to the registry.  This
bundles the ownership relation `OwnsKey` together with the assumption that an
owned key is published in the registry under its `pkOf`. -/
structure KeyEnvironment (kem : KEM) (reg : Registry) where
  /-- `OwnsKey u sk` means user `u` owns secret key `sk`. -/
  OwnsKey : UserId → SecretKey → Prop
  /-- An owned key's public key is exactly what the registry publishes. -/
  owns_key_lookup :
    ∀ u sk, OwnsKey u sk → reg.lookup u = some (kem.pkOf sk)

/-- Restatement of the environment invariant as a standalone lemma. -/
theorem owns_key_lookup {kem : KEM} {reg : Registry}
    (env : KeyEnvironment kem reg) {u : UserId} {sk : SecretKey}
    (h : env.OwnsKey u sk) :
    reg.lookup u = some (kem.pkOf sk) :=
  env.owns_key_lookup u sk h

end ChannelEstablishment

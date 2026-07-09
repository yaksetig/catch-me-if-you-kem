import Mathlib

/-!
# ChannelEstablishment.Types

Abstract carrier types for the channel-establishment protocol, together with the
protocol data objects (`ChannelAttempt`, `PublishedMessage`, `EstablishedChannel`).

All cryptographic carrier types are kept fully abstract by bundling them into a
single typeclass `ProtocolTypes`.  This keeps the development general: nothing in
the protocol logic depends on the concrete representation of keys, ciphertexts,
etc.  A concrete example `UserId` type is provided but *not* baked into the
development.
-/

namespace ChannelEstablishment

/-- All abstract carrier types used by the protocol, bundled as a typeclass so
that downstream definitions can stay uniform and instance-driven. -/
class ProtocolTypes where
  /-- Identities of registered users. -/
  UserId : Type
  /-- KEM public keys. -/
  PublicKey : Type
  /-- KEM secret keys. -/
  SecretKey : Type
  /-- KEM ciphertexts (the encapsulation `c₁`). -/
  Ciphertext1 : Type
  /-- AEAD ciphertexts (the payload ciphertext `c₂`). -/
  Ciphertext2 : Type
  /-- KEM shared secrets. -/
  SharedSecret : Type
  /-- AEAD keys (output of HKDF). -/
  AeadKey : Type
  /-- Setup payload plaintext. -/
  Payload : Type
  /-- HKDF context / info string. -/
  Context : Type
  /-- Bulletin-board activation arrays. -/
  ActivationArray : Type

open ProtocolTypes

/-- A concrete example identity type, matching the informal description.  It is
provided for illustration only; the protocol development is parametric over an
arbitrary `UserId`. -/
inductive ExampleUserId
  | Alice
  | Bob
  | Charlie
deriving DecidableEq, Repr

variable [T : ProtocolTypes]

/-- The full local state a sender produces for a single channel-establishment
attempt.  This records more than what is published (in particular the intended
`sender`, `recipient`, and the plaintext `payload`/`ss`); the published view is
obtained via `publish`. -/
structure ChannelAttempt where
  /-- The intended sender identity (local knowledge; never published). -/
  sender : UserId
  /-- The intended recipient identity (local knowledge; never published). -/
  recipient : UserId
  /-- The recipient public key used for encapsulation. -/
  recipientPk : PublicKey
  /-- The KEM shared secret produced by encapsulation. -/
  ss : SharedSecret
  /-- The KEM ciphertext `c₁`. -/
  c1 : Ciphertext1
  /-- The AEAD ciphertext `c₂`. -/
  c2 : Ciphertext2
  /-- The setup payload plaintext. -/
  payload : Payload
  /-- The HKDF context. -/
  context : Context
  /-- The activation array to publish. -/
  array : ActivationArray

/-- The public view of a channel attempt, i.e. exactly what is posted to the
bulletin board: `⟨c₁, c₂, array⟩`.  Crucially this carries *no* sender identity. -/
structure PublishedMessage where
  /-- The KEM ciphertext `c₁`. -/
  c1 : Ciphertext1
  /-- The AEAD ciphertext `c₂`. -/
  c2 : Ciphertext2
  /-- The activation array. -/
  array : ActivationArray

/-- The state a recipient obtains after successfully processing a board message.
Note there is no `sender` field: the recipient learns the shared secret and
payload, but *not* who created the message. -/
structure EstablishedChannel where
  /-- The recipient identity (the party that established the channel). -/
  recipient : UserId
  /-- The recovered KEM shared secret. -/
  ss : SharedSecret
  /-- The recovered payload plaintext. -/
  payload : Payload
  /-- The KEM ciphertext `c₁` that was processed. -/
  c1 : Ciphertext1
  /-- The AEAD ciphertext `c₂` that was processed. -/
  c2 : Ciphertext2
  /-- The HKDF context used. -/
  context : Context

end ChannelEstablishment

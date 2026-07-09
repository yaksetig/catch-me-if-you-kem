import ChannelEstablishment.Registry

/-!
# ChannelEstablishment.Protocol

The protocol algorithms: the sender step (`sendChannel`), the publication step
(`publish`), and the recipient step (`receiveChannel`), together with the
activation-array interface.
-/

namespace ChannelEstablishment

open ProtocolTypes

variable [T : ProtocolTypes]

/-- The activation-array interface.  `FullPrivacyArray` marks the "all ones"
full-privacy array; `Activated arr u` says the array activates user `u`'s slot.
The single assumption is that a full-privacy array activates *every* user, which
is exactly the recipient-independence that makes the array leak no slot. -/
structure Activation where
  /-- Predicate: the array is the full-privacy (`[1,…,1]`) array. -/
  FullPrivacyArray : ActivationArray → Prop
  /-- Predicate: the array activates user `u`'s slot. -/
  Activated : ActivationArray → UserId → Prop
  /-- A full-privacy array activates every user. -/
  full_privacy_activates_all :
    ∀ arr u, FullPrivacyArray arr → Activated arr u

/-- The sender step.  Looks up the recipient's public key in the registry,
encapsulates to it, derives an AEAD key from the shared secret and context, and
AEAD-encrypts the payload using the KEM ciphertext `c₁` as associated data.
Returns `none` if the recipient is not registered. -/
def sendChannel (kem : KEM) (hkdf : HKDF) (aead : AEAD) (reg : Registry)
    (ctx : Context) (arr : ActivationArray) (sender recipient : UserId)
    (m : Payload) : Option ChannelAttempt :=
  match reg.lookup recipient with
  | none => none
  | some pk =>
      let out := kem.encap pk
      let k := hkdf.derive out.1 ctx
      let c2 := aead.encrypt k m out.2
      some
        { sender := sender
          recipient := recipient
          recipientPk := pk
          ss := out.1
          c1 := out.2
          c2 := c2
          payload := m
          context := ctx
          array := arr }

/-- The publication step: project a channel attempt to its public view. -/
def publish (attempt : ChannelAttempt) : PublishedMessage :=
  { c1 := attempt.c1
    c2 := attempt.c2
    array := attempt.array }

/-- The recipient step.  Decapsulates `c₁` with the recipient secret key, derives
the AEAD key, and decrypts `c₂` using `c₁` as associated data.  Returns `none` on
any failure.  (The activation check is a *scanning precondition* handled at the
theorem level, since `Activated` is an abstract predicate; the recipient only
runs this on messages whose array activates its slot.) -/
def receiveChannel (kem : KEM) (hkdf : HKDF) (aead : AEAD)
    (ctx : Context) (recipient : UserId) (sk : SecretKey)
    (msg : PublishedMessage) : Option EstablishedChannel :=
  match kem.decap sk msg.c1 with
  | none => none
  | some ss =>
      let k := hkdf.derive ss ctx
      match aead.decrypt k msg.c2 msg.c1 with
      | none => none
      | some m =>
          some
            { recipient := recipient
              ss := ss
              payload := m
              c1 := msg.c1
              c2 := msg.c2
              context := ctx }

/-- The published transcript produced by a sender who encapsulates to public key
`pk` with payload `m`, context `ctx`, and array `arr`.  This equals
`publish` of a successful `sendChannel` (see `Security`), and is the object over
which recipient-privacy indistinguishability is stated. -/
def senderTranscript (kem : KEM) (hkdf : HKDF) (aead : AEAD)
    (ctx : Context) (arr : ActivationArray) (pk : PublicKey)
    (m : Payload) : PublishedMessage :=
  let out := kem.encap pk
  { c1 := out.2
    c2 := aead.encrypt (hkdf.derive out.1 ctx) m out.2
    array := arr }

end ChannelEstablishment

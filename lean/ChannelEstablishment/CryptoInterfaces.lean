import ChannelEstablishment.Types

/-!
# ChannelEstablishment.CryptoInterfaces

Abstract cryptographic interfaces used by the protocol.  We deliberately do
**not** attempt to prove ML-KEM, HKDF, or AEAD secure from first principles.
Instead each primitive is modeled as a structure bundling its operations
together with its correctness / security *assumptions* as fields.  Every
protocol-level theorem then follows from these explicitly named assumptions.

The KEM is modeled with a *deterministic* `encap`.  This is without loss of
generality here: a randomized KEM is recovered by taking `PublicKey`'s carrier to
already include the randomness, or by threading an explicit `KemRand`.  We
include a `KEMRandomized` variant that makes randomness explicit, and show the
deterministic interface is a special case.
-/

namespace ChannelEstablishment

open ProtocolTypes

variable [T : ProtocolTypes]

/-- Key-encapsulation mechanism.  `encap` is deterministic (see file docstring);
`decap` may fail (`Option`).  `pkOf` recovers the public key of a secret key.
The single assumption is *decapsulation correctness*. -/
structure KEM where
  /-- Encapsulate to a public key, producing a shared secret and ciphertext. -/
  encap : PublicKey → SharedSecret × Ciphertext1
  /-- Decapsulate a ciphertext with a secret key; may fail. -/
  decap : SecretKey → Ciphertext1 → Option SharedSecret
  /-- The public key associated to a secret key. -/
  pkOf  : SecretKey → PublicKey
  /-- Correctness: decapsulating an honest encapsulation to `pkOf sk` recovers
  the encapsulated shared secret. -/
  correctness :
    ∀ sk : SecretKey,
      decap sk (encap (pkOf sk)).2 = some (encap (pkOf sk)).1

/-- A randomized KEM interface, making encapsulation randomness explicit.  This
is provided to document the general shape; the protocol development uses the
deterministic `KEM` interface, which `ofRandomized` shows is the special case of
a fixed randomness value. -/
structure KEMRandomized (R : Type) where
  /-- Randomized encapsulation. -/
  encap : PublicKey → R → SharedSecret × Ciphertext1
  /-- Decapsulation; may fail. -/
  decap : SecretKey → Ciphertext1 → Option SharedSecret
  /-- Public key of a secret key. -/
  pkOf  : SecretKey → PublicKey
  /-- Correctness for every randomness value. -/
  correctness :
    ∀ (sk : SecretKey) (r : R),
      decap sk (encap (pkOf sk) r).2 = some (encap (pkOf sk) r).1

/-- Any randomized KEM specialized at a fixed randomness value yields a
deterministic `KEM`, preserving correctness. -/
def KEMRandomized.ofRandomized {R : Type} (K : KEMRandomized R) (r : R) : KEM where
  encap := fun pk => K.encap pk r
  decap := K.decap
  pkOf := K.pkOf
  correctness := fun sk => K.correctness sk r

/-- HKDF, modeled as a deterministic key-derivation function. -/
structure HKDF where
  /-- Derive an AEAD key from a shared secret and a context. -/
  derive : SharedSecret → Context → AeadKey

/-- Authenticated encryption with associated data.  `encrypt` is deterministic
(again w.l.o.g., or with randomness folded into the key/payload).  Two
assumptions:

* `correctness`: decrypting a fresh encryption under matching key and AD recovers
  the plaintext.
* `ad_binding`: if a ciphertext decrypts successfully under associated data
  `ad'`, then `ad'` must equal the associated data used to produce it.  This
  models *integrity of associated data*: the AEAD cryptographically binds `c₂` to
  the AD it was created with.  It is a standard consequence of AEAD
  authenticity (ciphertext + AD integrity); we surface it here as an explicit,
  auditable assumption. -/
structure AEAD where
  /-- Encrypt a payload under a key with associated data. -/
  encrypt : AeadKey → Payload → Ciphertext1 → Ciphertext2
  /-- Decrypt a ciphertext under a key with associated data; may fail. -/
  decrypt : AeadKey → Ciphertext2 → Ciphertext1 → Option Payload
  /-- Correctness of authenticated decryption. -/
  correctness :
    ∀ k m ad, decrypt k (encrypt k m ad) ad = some m
  /-- Associated-data binding (integrity of AD). -/
  ad_binding :
    ∀ k m ad ad',
      decrypt k (encrypt k m ad) ad' = some m → ad' = ad

end ChannelEstablishment

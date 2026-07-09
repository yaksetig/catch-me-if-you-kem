import ChannelEstablishment.Protocol

/-!
# ChannelEstablishment.Security

The positive protocol-level theorems: correctness, registry provenance,
publication shape, full-privacy activation, AEAD associated-data binding,
recipient decapsulation, channel agreement, and a closed-world Bob-origin
theorem.  Also the (non-cryptographic) activation-array leakage property and a
formal *dependency* theorem showing recipient anonymity of the full transcript
requires a key-private KEM.

All results are consequences of the explicit assumptions bundled in the
`KEM`, `AEAD`, `Activation`, and (for privacy) `KEMKeyPrivate` / `AEADPrivacy`
interfaces.  Nothing here assumes any primitive secure "from first principles".
-/

namespace ChannelEstablishment

open ProtocolTypes

variable [T : ProtocolTypes]

/-! ## Characterization lemmas for the protocol steps -/

/-- Full characterization of a successful `sendChannel`: the recipient was
registered, and every field of the produced attempt is determined. -/
theorem sendChannel_success
    {kem : KEM} {hkdf : HKDF} {aead : AEAD} {reg : Registry}
    {ctx : Context} {arr : ActivationArray} {sender recipient : UserId}
    {m : Payload} {attempt : ChannelAttempt}
    (h : sendChannel kem hkdf aead reg ctx arr sender recipient m = some attempt) :
    reg.lookup recipient = some attempt.recipientPk ∧
    attempt.sender = sender ∧
    attempt.recipient = recipient ∧
    attempt.ss = (kem.encap attempt.recipientPk).1 ∧
    attempt.c1 = (kem.encap attempt.recipientPk).2 ∧
    attempt.c2 = aead.encrypt (hkdf.derive attempt.ss ctx) m attempt.c1 ∧
    attempt.payload = m ∧
    attempt.context = ctx ∧
    attempt.array = arr := by
  cases hl : reg.lookup recipient with
  | none => simp [sendChannel, hl] at h
  | some pk =>
      simp only [sendChannel, hl, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Full characterization of a successful `receiveChannel`: decapsulation and
decryption both succeeded, and the established channel is determined. -/
theorem receiveChannel_success
    {kem : KEM} {hkdf : HKDF} {aead : AEAD} {ctx : Context}
    {recipient : UserId} {sk : SecretKey} {msg : PublishedMessage}
    {established : EstablishedChannel}
    (h : receiveChannel kem hkdf aead ctx recipient sk msg = some established) :
    ∃ ss m,
      kem.decap sk msg.c1 = some ss ∧
      aead.decrypt (hkdf.derive ss ctx) msg.c2 msg.c1 = some m ∧
      established =
        { recipient := recipient, ss := ss, payload := m,
          c1 := msg.c1, c2 := msg.c2, context := ctx } := by
  simp only [receiveChannel] at h
  split at h
  · exact absurd h (by simp)
  · rename_i ss hd
    split at h
    · exact absurd h (by simp)
    · rename_i m he
      simp only [Option.some.injEq] at h
      exact ⟨ss, m, hd, he, h.symm⟩

/-! ## 11.2 Registry provenance -/

/-- A successful sender attempt uses the recipient public key obtained from the
registry. -/
theorem send_uses_registered_recipient_key
    {kem : KEM} {hkdf : HKDF} {aead : AEAD} {reg : Registry}
    {ctx : Context} {arr : ActivationArray} {sender recipient : UserId}
    {m : Payload} {attempt : ChannelAttempt}
    (h : sendChannel kem hkdf aead reg ctx arr sender recipient m = some attempt) :
    reg.lookup recipient = some attempt.recipientPk :=
  (sendChannel_success h).1

/-! ## 11.3 Publication shape -/

/-- Publication copies exactly the `c₁`, `c₂`, and `array` fields. -/
theorem published_message_matches_attempt
    {attempt : ChannelAttempt} {msg : PublishedMessage}
    (h : publish attempt = msg) :
    msg.c1 = attempt.c1 ∧ msg.c2 = attempt.c2 ∧ msg.array = attempt.array := by
  subst h; exact ⟨rfl, rfl, rfl⟩

/-! ## 11.4 Full-privacy array publication -/

/-- A sender who supplies a full-privacy array publishes a full-privacy array. -/
theorem send_uses_full_privacy_array
    {kem : KEM} {hkdf : HKDF} {aead : AEAD} {reg : Registry}
    {ctx : Context} {arr : ActivationArray} {sender recipient : UserId}
    {m : Payload} {attempt : ChannelAttempt}
    (activation : Activation)
    (hfp : activation.FullPrivacyArray arr)
    (h : sendChannel kem hkdf aead reg ctx arr sender recipient m = some attempt) :
    activation.FullPrivacyArray attempt.array := by
  obtain ⟨_, _, _, _, _, _, _, _, harr⟩ := sendChannel_success h
  rw [harr]; exact hfp

/-- A full-privacy array activates the intended recipient. -/
theorem full_privacy_activates_recipient
    (activation : Activation) {attempt : ChannelAttempt}
    (h : activation.FullPrivacyArray attempt.array) :
    activation.Activated attempt.array attempt.recipient :=
  activation.full_privacy_activates_all _ _ h

/-- Restatement (§7): a full-privacy array activates every user. -/
theorem full_privacy_activates_all
    (activation : Activation) (arr : ActivationArray) (u : UserId)
    (h : activation.FullPrivacyArray arr) :
    activation.Activated arr u :=
  activation.full_privacy_activates_all arr u h

/-- Restatement (§7): under a full-privacy array, activation is
recipient-independent. -/
theorem full_privacy_array_recipient_independent
    (activation : Activation) (arr : ActivationArray) (u v : UserId)
    (h : activation.FullPrivacyArray arr) :
    activation.Activated arr u ↔ activation.Activated arr v :=
  ⟨fun _ => activation.full_privacy_activates_all arr v h,
   fun _ => activation.full_privacy_activates_all arr u h⟩

/-! ## 11.5 AEAD associated-data binding -/

/-- The established channel's ciphertexts are exactly those in the board message. -/
theorem established_ciphertext_bound_to_c1
    {kem : KEM} {hkdf : HKDF} {aead : AEAD} {ctx : Context}
    {recipient : UserId} {sk : SecretKey} {msg : PublishedMessage}
    {established : EstablishedChannel}
    (h : receiveChannel kem hkdf aead ctx recipient sk msg = some established) :
    established.c1 = msg.c1 ∧ established.c2 = msg.c2 := by
  obtain ⟨_, _, _, _, heq⟩ := receiveChannel_success h
  subst heq; exact ⟨rfl, rfl⟩

/-- Successful decryption used `msg.c1` (equivalently `established.c1`) as the
associated data. -/
theorem established_decrypt_uses_c1_as_ad
    {kem : KEM} {hkdf : HKDF} {aead : AEAD} {ctx : Context}
    {recipient : UserId} {sk : SecretKey} {msg : PublishedMessage}
    {established : EstablishedChannel}
    (h : receiveChannel kem hkdf aead ctx recipient sk msg = some established) :
    ∃ k : AeadKey,
      aead.decrypt k established.c2 established.c1 = some established.payload := by
  obtain ⟨ss, m, _, he, heq⟩ := receiveChannel_success h
  subst heq
  exact ⟨hkdf.derive ss ctx, he⟩

/-- Direct use of the AEAD `ad_binding` assumption: if the AEAD ciphertext
produced for `attempt` decrypts successfully under some associated data `ad'`,
then `ad'` must be the `c₁` it was created with. -/
theorem aead_ad_binding_channel
    {kem : KEM} {hkdf : HKDF} {aead : AEAD} {reg : Registry}
    {ctx : Context} {arr : ActivationArray} {sender recipient : UserId}
    {m : Payload} {attempt : ChannelAttempt}
    (hsend : sendChannel kem hkdf aead reg ctx arr sender recipient m = some attempt)
    {ad' : Ciphertext1}
    (hdec : aead.decrypt (hkdf.derive attempt.ss ctx) attempt.c2 ad' = some m) :
    ad' = attempt.c1 := by
  obtain ⟨_, _, _, _, _, hc2, _, _, _⟩ := sendChannel_success hsend
  rw [hc2] at hdec
  exact aead.ad_binding _ _ _ _ hdec

/-! ## 11.6 Recipient decapsulation -/

/-- If a channel is established, the KEM ciphertext decapsulated successfully
under the recipient secret key, yielding the established shared secret. -/
theorem receive_success_implies_decap_success
    {kem : KEM} {hkdf : HKDF} {aead : AEAD} {ctx : Context}
    {recipient : UserId} {sk : SecretKey} {msg : PublishedMessage}
    {established : EstablishedChannel}
    (h : receiveChannel kem hkdf aead ctx recipient sk msg = some established) :
    ∃ ss, kem.decap sk msg.c1 = some ss ∧ established.ss = ss := by
  obtain ⟨ss, m, hd, _, heq⟩ := receiveChannel_success h
  exact ⟨ss, hd, by subst heq; rfl⟩

/-! ## 11.1 / 11.7 Correctness and channel agreement -/

/-- **Channel agreement (main correctness theorem).**  If Bob sends to Alice
using Alice's registered public key, publishes, and Alice (owning the matching
secret key) receives, then Alice recovers exactly Bob's shared secret and
payload. -/
theorem sender_recipient_agree_on_secret_and_payload
    (kem : KEM) (hkdf : HKDF) (aead : AEAD) (reg : Registry)
    (ctx : Context) (arr : ActivationArray) (bob alice : UserId)
    (payload : Payload) (attempt : ChannelAttempt) (msg : PublishedMessage)
    (skA : SecretKey) (established : EstablishedChannel)
    (hsend : sendChannel kem hkdf aead reg ctx arr bob alice payload = some attempt)
    (hpub : publish attempt = msg)
    (hrecv : receiveChannel kem hkdf aead ctx alice skA msg = some established)
    (hkey : reg.lookup alice = some (kem.pkOf skA)) :
    established.ss = attempt.ss ∧ established.payload = attempt.payload := by
  subst hpub
  simp only [sendChannel, hkey, Option.some.injEq] at hsend
  subst hsend
  simp only [publish, receiveChannel, kem.correctness, aead.correctness,
    Option.some.injEq] at hrecv
  subst hrecv
  exact ⟨rfl, rfl⟩

/-- **Channel correctness (§11.1).**  Under a full-privacy array and Alice's
registered key, Alice is activated and her `receiveChannel` on the published
attempt succeeds, returning the shared secret and payload Bob produced. -/
theorem channel_correctness
    (kem : KEM) (hkdf : HKDF) (aead : AEAD) (reg : Registry)
    (activation : Activation)
    (ctx : Context) (arr : ActivationArray) (bob alice : UserId)
    (payload : Payload) (attempt : ChannelAttempt) (skA : SecretKey)
    (hfp : activation.FullPrivacyArray arr)
    (hsend : sendChannel kem hkdf aead reg ctx arr bob alice payload = some attempt)
    (hkey : reg.lookup alice = some (kem.pkOf skA)) :
    activation.Activated arr alice ∧
    receiveChannel kem hkdf aead ctx alice skA (publish attempt) =
      some
        { recipient := alice, ss := attempt.ss, payload := attempt.payload,
          c1 := attempt.c1, c2 := attempt.c2, context := ctx } := by
  refine ⟨activation.full_privacy_activates_all arr alice hfp, ?_⟩
  simp only [sendChannel, hkey, Option.some.injEq] at hsend
  subst hsend
  simp only [publish, receiveChannel, kem.correctness, aead.correctness]

/-! ## 11.8 Closed-world Bob-origin theorem -/

/-- **Closed-world / trace-local theorem.**  In a world whose board contains
*exactly one* message, namely `publish attempt` produced by Bob, if Alice
establishes a channel from that message (with her registered key), then the
established channel corresponds to Bob's attempt: same ciphertexts, same shared
secret, same payload, and its origin is Bob.

⚠️ This is **not** a real-world sender-authentication theorem.  It holds only
because the world is *stipulated* to contain a single Bob-produced message; it
says nothing about an adversary who posts their own `⟨c₁,c₂,array⟩`.  See
`ChannelEstablishment.Limitations` for the impossibility of authenticating the
sender from the published message alone. -/
theorem closed_world_alice_established_from_bob_attempt
    (kem : KEM) (hkdf : HKDF) (aead : AEAD) (reg : Registry)
    (ctx : Context) (arr : ActivationArray) (bob alice : UserId)
    (payload : Payload) (attempt : ChannelAttempt) (msg : PublishedMessage)
    (skA : SecretKey) (established : EstablishedChannel)
    (hsend : sendChannel kem hkdf aead reg ctx arr bob alice payload = some attempt)
    (hbob : attempt.sender = bob)
    (honly : msg = publish attempt)
    (hrecv : receiveChannel kem hkdf aead ctx alice skA msg = some established)
    (hkey : reg.lookup alice = some (kem.pkOf skA)) :
    attempt.sender = bob ∧
    established.c1 = attempt.c1 ∧ established.c2 = attempt.c2 ∧
    established.ss = attempt.ss ∧ established.payload = attempt.payload := by
  subst honly
  have hbind := established_ciphertext_bound_to_c1 hrecv
  have hagree :=
    sender_recipient_agree_on_secret_and_payload kem hkdf aead reg ctx arr bob alice
      payload attempt (publish attempt) skA established hsend rfl hrecv hkey
  refine ⟨hbob, ?_, ?_, hagree.1, hagree.2⟩
  · rw [hbind.1]; rfl
  · rw [hbind.2]; rfl

/-! ## 13 Activation-array leakage (non-cryptographic shape property) -/

/-- The activation array alone does not distinguish any two users when it is a
full-privacy array: both are activated. -/
theorem full_array_leaks_no_slot_information
    (activation : Activation) (arr : ActivationArray) (u v : UserId)
    (h : activation.FullPrivacyArray arr) :
    activation.Activated arr u ↔ activation.Activated arr v :=
  full_privacy_array_recipient_independent activation arr u v h

/-! ## 13 Transcript recipient privacy from a key-private KEM -/

/-- An abstract transcript-indistinguishability relation (an equivalence
relation on published messages).  Cryptographic content is deferred to the
`KEMKeyPrivate` / `AEADPrivacy` assumptions below; here we only require it be an
equivalence. -/
structure IndistinguishabilityModel where
  /-- The indistinguishability relation on published transcripts. -/
  Indist : PublishedMessage → PublishedMessage → Prop
  /-- Reflexivity. -/
  refl : ∀ t, Indist t t
  /-- Symmetry. -/
  symm : ∀ {t u}, Indist t u → Indist u t
  /-- Transitivity. -/
  trans : ∀ {t u v}, Indist t u → Indist u v → Indist t v

/-- KEM key-privacy / recipient anonymity, at the transcript level: swapping the
recipient public key (hence the KEM ciphertext `c₁`) leaves the transcript
indistinguishable, for any fixed `c₂` and array. -/
structure KEMKeyPrivate (kem : KEM) (I : IndistinguishabilityModel) : Prop where
  /-- Encapsulations to different public keys are indistinguishable. -/
  encap_indist :
    ∀ (pk1 pk2 : PublicKey) (c2 : Ciphertext2) (arr : ActivationArray),
      I.Indist ⟨(kem.encap pk1).2, c2, arr⟩ ⟨(kem.encap pk2).2, c2, arr⟩

/-- AEAD privacy: an honest AEAD ciphertext is indistinguishable from a fixed
simulator ciphertext `Sim` (independent of key, payload, and associated data),
with `c₁` and array held fixed.  This is the transcript-level shape of AEAD
ciphertext indistinguishability. -/
structure AEADPrivacy (aead : AEAD) (I : IndistinguishabilityModel) where
  /-- A simulator ciphertext carrying no information about key/payload/AD. -/
  Sim : Ciphertext2
  /-- Honest ciphertexts are indistinguishable from `Sim`. -/
  encrypt_indist :
    ∀ (k : AeadKey) (m : Payload) (c1 : Ciphertext1) (arr : ActivationArray),
      I.Indist ⟨c1, aead.encrypt k m c1, arr⟩ ⟨c1, Sim, arr⟩

/-- **Recipient privacy of the full transcript from a key-private KEM.**  Given
KEM key-privacy and AEAD privacy, the transcripts for `Bob → Alice` and
`Bob → Charlie` (with possibly different payloads) are indistinguishable.  The
proof is a two-hop hybrid: replace each honest AEAD ciphertext by the simulator
`Sim`, then swap the KEM ciphertext using key-privacy.

The full-privacy array hypothesis `_hfp` is included because it is part of the
protocol's operating mode; it is not needed for the algebraic argument, since
both transcripts already carry the *same* array. -/
theorem transcript_recipient_privacy_from_key_private_kem
    (kem : KEM) (hkdf : HKDF) (aead : AEAD) (activation : Activation)
    (I : IndistinguishabilityModel)
    (hkem : KEMKeyPrivate kem I) (haead : AEADPrivacy aead I)
    (ctx : Context) (arr : ActivationArray)
    (pkA pkC : PublicKey) (mA mC : Payload)
    (_hfp : activation.FullPrivacyArray arr) :
    I.Indist (senderTranscript kem hkdf aead ctx arr pkA mA)
             (senderTranscript kem hkdf aead ctx arr pkC mC) := by
  simp only [senderTranscript]
  have h1 := haead.encrypt_indist (hkdf.derive (kem.encap pkA).1 ctx) mA
    (kem.encap pkA).2 arr
  have h2 := hkem.encap_indist pkA pkC haead.Sim arr
  have h3 := haead.encrypt_indist (hkdf.derive (kem.encap pkC).1 ctx) mC
    (kem.encap pkC).2 arr
  exact I.trans h1 (I.trans h2 (I.symm h3))

/-- **Recipient privacy requires KEM key-privacy (formal dependency).**  In the
*discrete* indistinguishability model (`Indist = (· = ·)`, i.e. no cryptographic
hiding at all), the recipient transcripts for two public keys can only be
indistinguishable if the KEM ciphertexts literally coincide.  Contrapositively,
whenever `(kem.encap pkA).2 ≠ (kem.encap pkC).2` — the generic situation for a
non-anonymous KEM — the transcripts are distinguishable.  Hence hiding the
recipient genuinely requires a key-private / recipient-anonymous KEM such as
`KEMKeyPrivate`. -/
theorem recipient_privacy_requires_kem_key_privacy
    (kem : KEM) (hkdf : HKDF) (aead : AEAD)
    (ctx : Context) (arr : ActivationArray)
    (pkA pkC : PublicKey) (mA mC : Payload)
    (I : IndistinguishabilityModel)
    (hI : I.Indist = fun a b => a = b)
    (h : I.Indist (senderTranscript kem hkdf aead ctx arr pkA mA)
                  (senderTranscript kem hkdf aead ctx arr pkC mC)) :
    (kem.encap pkA).2 = (kem.encap pkC).2 := by
  rw [hI] at h
  simp only [senderTranscript] at h
  exact congrArg PublishedMessage.c1 h

end ChannelEstablishment

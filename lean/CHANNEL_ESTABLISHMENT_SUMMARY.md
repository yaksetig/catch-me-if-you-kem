# Channel Establishment — Formalization Summary

A Lean 4 + Mathlib formalization of the KEM-based channel-establishment protocol
(Bob → Alice via a public registry and a bulletin board), with correctness,
provenance, binding, and privacy-shape theorems proved under clean abstract
cryptographic interfaces.

The development builds with no `sorry`, no `admit`, and no new global `axiom`.
Every cryptographic assumption is an explicit **structure field** or **theorem
hypothesis** (audited below). Machine-checked axiom footprint is limited to
`propext` (and `Classical.choice`/`Quot.sound` via Mathlib where applicable).

## Files

```
ChannelEstablishment/Types.lean            -- abstract carrier types + protocol data objects
ChannelEstablishment/CryptoInterfaces.lean -- KEM, HKDF, AEAD (with correctness/security fields)
ChannelEstablishment/Registry.lean         -- public registry + key-ownership environment
ChannelEstablishment/Protocol.lean         -- sendChannel / publish / receiveChannel + activation interface
ChannelEstablishment/Security.lean         -- positive theorems + transcript-privacy dependency
ChannelEstablishment/Limitations.lean      -- no-sender-authentication + recipient-privacy caveat
ChannelEstablishment.lean                  -- aggregator importing all modules
```

## What was formalized

* **Abstract carrier types** (`ProtocolTypes` typeclass): `UserId`, `PublicKey`,
  `SecretKey`, `Ciphertext1`, `Ciphertext2`, `SharedSecret`, `AeadKey`,
  `Payload`, `Context`, `ActivationArray`. Nothing depends on their concrete
  representation. A concrete `ExampleUserId := Alice | Bob | Charlie` is provided
  for illustration but not baked in.
* **Protocol objects**: `ChannelAttempt` (sender-local state), `PublishedMessage`
  (`⟨c₁, c₂, array⟩`, carries **no** sender identity), `EstablishedChannel`
  (recipient state, no sender field).
* **Protocol steps**: `sendChannel` (lookup → encapsulate → HKDF → AEAD-encrypt
  with `c₁` as associated data), `publish` (projection to the public view),
  `receiveChannel` (decapsulate → HKDF → AEAD-decrypt with `c₁` as AD).

## Assumptions used (all explicit, all localized)

* `KEM.correctness`: `decap sk (encap (pkOf sk)).2 = some (encap (pkOf sk)).1`.
  (A randomized variant `KEMRandomized` is provided, with `ofRandomized` showing
  the deterministic interface is its fixed-randomness specialization.)
* `AEAD.correctness`: `decrypt k (encrypt k m ad) ad = some m`.
* `AEAD.ad_binding`: `decrypt k (encrypt k m ad) ad' = some m → ad' = ad`
  (integrity of associated data — surfaced as an explicit, auditable field).
* `Activation.full_privacy_activates_all`: a full-privacy array activates every
  user.
* `Registry.lookup_registered`; `KeyEnvironment.owns_key_lookup` (owned key is
  registered under its `pkOf`).
* For transcript privacy only: `KEMKeyPrivate` (KEM key-privacy / recipient
  anonymity) and `AEADPrivacy` (AEAD ciphertext indistinguishable from a
  simulator), over an abstract equivalence-relation `IndistinguishabilityModel`.

We do **not** attempt to prove ML-KEM, HKDF, or AEAD secure from first
principles; they are modeled as interfaces and the protocol theorems follow from
the assumptions above.

## Theorems proved

Correctness / provenance / binding / shape (all required names present):

* `channel_correctness` — Alice is activated and her receive on the published
  attempt returns Bob's shared secret and payload.
* `sender_recipient_agree_on_secret_and_payload` — main correctness: established
  `ss`/`payload` equal the sender's.
* `send_uses_registered_recipient_key` — the attempt uses the registry key.
* `published_message_matches_attempt` — publication copies `c₁`, `c₂`, `array`.
* `send_uses_full_privacy_array`, `full_privacy_activates_recipient`,
  `full_privacy_activates_all`, `full_privacy_array_recipient_independent`.
* `established_ciphertext_bound_to_c1`, `established_decrypt_uses_c1_as_ad`,
  `aead_ad_binding_channel` (direct use of the AEAD AD-binding assumption).
* `receive_success_implies_decap_success` — successful receive ⇒ decap succeeded.
* `closed_world_alice_established_from_bob_attempt` — **closed-world / trace-local
  only**; explicitly *not* real sender authentication.
* `full_array_leaks_no_slot_information` — activation array leaks no slot in
  full-privacy mode.
* `transcript_recipient_privacy_from_key_private_kem` — full-transcript recipient
  privacy under `KEMKeyPrivate` + `AEADPrivacy` (two-hop hybrid).
* `recipient_privacy_requires_kem_key_privacy` — formal dependency: without
  cryptographic hiding, transcript indistinguishability forces equal KEM
  ciphertexts (so a non-anonymous KEM leaks the recipient).

Limitations (negative results):

* `sender_identity_not_encoded_in_published_message`.
* `same_publication_different_sender_possible`.
* `published_message_does_not_authenticate_sender` — no function on the published
  message alone recovers the sender.

## Properties that cannot be proved from the protocol as written

* **Sender authentication is absent.** The published message `⟨c₁, c₂, [1..1]⟩`
  carries no sender identity, so "if Alice establishes a channel, then Bob
  created it" is **false** in the open world and is deliberately not proved. It is
  refuted by `published_message_does_not_authenticate_sender` /
  `same_publication_different_sender_possible`. A Bob-origin conclusion holds only
  in the stipulated closed world (`closed_world_alice_established_from_bob_attempt`).
  Real sender authentication requires an authenticated credential / signature /
  MAC inside the payload.
* **Activation-array privacy ≠ recipient anonymity.** `full_array_leaks_no_slot_information`
  concerns only the array. Downloading the full registry hides Bob's *lookup*
  behavior (registry-lookup privacy), but the KEM ciphertext `c₁` can still leak
  the recipient. `recipient_privacy_requires_kem_key_privacy` shows recipient
  hiding genuinely needs a key-private / recipient-anonymous KEM (or an extra
  wrapping mechanism); `transcript_recipient_privacy_from_key_private_kem`
  recovers it only under those explicit assumptions.

import ChannelEstablishment.Security

/-!
# ChannelEstablishment.Limitations

Negative / limitation results.  The protocol as written **does not authenticate
the sender**: the published message `⟨c₁, c₂, [1,…,1]⟩` carries no sender
identity, so no procedure operating on the published message alone can recover
who sent it.  We also record the recipient-privacy caveat: activation-array
privacy does *not* imply full recipient anonymity.

These theorems are the formal justification for **not** proving the (false)
statement "if Alice establishes a channel, then Bob created it".
-/

namespace ChannelEstablishment

open ProtocolTypes

variable [T : ProtocolTypes]

/-- The published message is a function of `(c₁, c₂, array)` only: two attempts
agreeing on those three fields publish identical messages, regardless of sender,
recipient, shared secret, payload, or context. -/
theorem sender_identity_not_encoded_in_published_message
    (attempt1 attempt2 : ChannelAttempt)
    (h1 : attempt1.c1 = attempt2.c1)
    (h2 : attempt1.c2 = attempt2.c2)
    (h3 : attempt1.array = attempt2.array) :
    publish attempt1 = publish attempt2 := by
  simp only [publish, h1, h2, h3]

/-- Two channel attempts with **different senders** can produce the **same**
published message.  (We take any single attempt `a` and any two distinct users;
overriding only the `sender` field leaves the publication unchanged.)  This shows
`PublishedMessage` does not carry sender identity. -/
theorem same_publication_different_sender_possible
    (s1 s2 : UserId) (hne : s1 ≠ s2) (a : ChannelAttempt) :
    ∃ attempt1 attempt2 : ChannelAttempt,
      attempt1.sender ≠ attempt2.sender ∧ publish attempt1 = publish attempt2 := by
  refine ⟨{a with sender := s1}, {a with sender := s2}, ?_, ?_⟩
  · simpa using hne
  · simp only [publish]

/-- **No sender authentication from the published message.**  There is no
function `recover : PublishedMessage → UserId` that soundly returns the sender of
every attempt: given two distinct users, the two publications that differ only in
sender are equal, so any such `recover` would have to return both senders on the
same input. -/
theorem published_message_does_not_authenticate_sender
    (s1 s2 : UserId) (hne : s1 ≠ s2) (a : ChannelAttempt) :
    ¬ ∃ recover : PublishedMessage → UserId,
        ∀ att : ChannelAttempt, recover (publish att) = att.sender := by
  rintro ⟨recover, hrec⟩
  have e1 := hrec {a with sender := s1}
  have e2 := hrec {a with sender := s2}
  have hpub :
      publish ({a with sender := s1} : ChannelAttempt)
        = publish ({a with sender := s2} : ChannelAttempt) := by
    simp only [publish]
  rw [hpub] at e1
  exact hne (e1.symm.trans e2)

/-!
## Recipient-privacy caveat (informal, backed by `Security`)

Downloading the *full* registry hides Bob's **lookup** behavior: the server /
network learns nothing about which entry Bob consulted.  This is genuine
*registry-lookup privacy*.

It must **not** be confused with cryptographic *recipient anonymity* of the
published transcript.  The published KEM ciphertext `c₁` may reveal the recipient
unless the KEM is key-private / recipient-anonymous.  Formally:

* `ChannelEstablishment.full_array_leaks_no_slot_information` shows the activation
  array alone leaks no slot in full-privacy mode; but this concerns only the
  array, not `c₁`/`c₂`.
* `ChannelEstablishment.recipient_privacy_requires_kem_key_privacy` shows that,
  absent cryptographic hiding, indistinguishability of the recipient transcripts
  forces the KEM ciphertexts to coincide — i.e. a non-anonymous KEM leaks the
  recipient.
* `ChannelEstablishment.transcript_recipient_privacy_from_key_private_kem`
  recovers full-transcript recipient privacy, but only under the explicit
  `KEMKeyPrivate` and `AEADPrivacy` assumptions.

Thus recipient privacy of the transcript needs a key-private / recipient-anonymous
KEM (or an additional wrapping mechanism); it does not follow from the
activation-array shape property alone.
-/

end ChannelEstablishment

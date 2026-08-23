# DRAFT PR body v2 - not pushed. Needs Sunny's approval.

Repo: VerifiedMechanisms/re-takehome (fork sunnyadn/re-takehome, branch allow-provider-fallbacks)
Title: Allow provider fallback so a sick provider does not zero the problem

---

Turns on provider fallback in the OpenRouter request, per #1.

Measured through the harness client just now, 20 identical small calls to `gpt-oss-120b` each way.

| | succeeded | served by |
| --- | --- | --- |
| as shipped | 3/20 | CoreWeave |
| patched | 20/20 | 6 different providers |

CoreWeave is the unhealthy one at the moment, yesterday it was AkashML.

Model fallback stays off, since the request never carries a `models` array, and the added assertion pins that. `require_parameters` is untouched.

Worth naming what it loosens. `max_price` bounds cost at the ceiling, and `PRICE_CEILINGS` sits deliberately above advertised prices, so a fallback can cost more than the primary would have. Across providers eligible today the completion price runs $0.17 to $0.50 per million,. They also run this model at quantizations from bf16 to fp4, so a wider pool is a wider mixture. None of them charges a per-request fee, which the reservation formula does not cover.

Suite passes, 24 tests, docker integration deselected locally.

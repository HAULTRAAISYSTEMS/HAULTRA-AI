# Yard container dispatch — issue #155

## Scope
The boss selects an existing company-owned yard container (e.g. #3063, 30yd) and explicitly selects its **physical condition** before dispatch. The existing `YARD` action is not sufficient to represent the job type.

## Dispatch choices

| Condition | Action | Job boundary | Container after completion |
| --- | --- | --- | --- |
| FULL | Dump only | Yard pickup -> landfill dump -> **job complete at landfill** | EMPTY, on truck at landfill |
| EMPTY | Direct delivery | Yard pickup -> customer drop -> **job complete at customer** | EMPTY, deployed at customer |
| FULL | Dump then deliver | Job 1: yard -> dump; Job 2: landfill -> customer | After Job 1: EMPTY on truck; after Job 2: deployed at customer |

The two jobs in dump-then-deliver must be separately completable and individually identifiable in daily routes. Never create an implicit return to the yard. The driver must confirm the physical operation before inventory changes.

## UI contract
Boss yard can picker: select container; show can number/size, current location, and condition; choose FULL/EMPTY; choose dump-only or dump-then-deliver when FULL, direct delivery when EMPTY; choose landfill or customer address as appropriate; select driver/truck; preview legs and **job boundaries**; dispatch only with required fields and an available container.

Driver cab: show yard hook, landfill dump or customer drop, and a distinct Complete Job transition. After dump-only completion, advance to the next assigned job; do not require a yard return. If dump fails, do not mark EMPTY or complete the job.

## Invariants
- Company-scoped container selection and mutations; no cross-tenant access.
- No duplicate container records or jobs on repeated dispatch/completion requests.
- Explicit condition and physical location are separate state dimensions; dump does not mean return-to-yard.
- Preserve legacy swap chains, explicit return-to-yard routes, and existing daily routes.
- Avoid automatically marking a full can empty until dump is confirmed.
- On job cancellation or failure, preserve the last confirmed physical state.

## Required regression tests before merge
1. FULL can -> dump-only -> complete at landfill -> next independent job.
2. EMPTY can -> customer direct delivery -> deployed at customer.
3. FULL can -> dump then deliver -> two separately completed jobs.
4. Failed/canceled dump does not mutate inventory condition.
5. Duplicate completion/refresh remains idempotent.
6. Existing swap chains and explicit yard returns remain unchanged.
7. Company isolation and container availability validation.
8. Cab completion on final leg advances without getting stuck.

This document is an implementation contract, **not** a completed feature. Do not merge it as a functional release until code and tests are in place.
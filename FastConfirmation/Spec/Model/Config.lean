import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Spec / Model / Config

Protocol constants and configuration consumed by the Fast Confirmation Rule
spec (`consensus-specs/specs/phase0/fast-confirmation.md` — "Constants" and
"Configuration" — plus the beacon-chain / fork-choice presets the rule reads).

Python `uint64` values are modelled as `ℕ` (see `docs/spec-model-design.md`,
decision 1). `GENESIS_SLOT = GENESIS_EPOCH = 0` are hardcoded below as in the
phase0 spec.
-/

namespace FastConfirmation.Spec

/-- Beacon-chain / fork-choice / FCR configuration values read by the Fast
Confirmation Rule. Mainnet values live in `mainnet_config`; keeping them as a
record (rather than global constants) lets theorems quantify over
configurations, mirroring the preset/config split of the specs. -/
structure Config where
  /-- `SLOTS_PER_EPOCH` (preset; mainnet `32`). -/
  slots_per_epoch : ℕ
  /-- Slots-per-epoch is positive (division by it appears throughout). -/
  slots_per_epoch_pos : 0 < slots_per_epoch
  /-- `SLOT_DURATION_MS` (config; mainnet `12000`). -/
  slot_duration_ms : ℕ
  /-- Slot duration is positive (`get_slots_since_genesis` divides by it). -/
  slot_duration_ms_pos : 0 < slot_duration_ms
  /-- `PROPOSER_SCORE_BOOST` (fork-choice config, percent; mainnet `40`). -/
  proposer_score_boost : ℕ
  /-- `CONFIRMATION_BYZANTINE_THRESHOLD` (FCR config, percent; mainnet `25`,
      which is also the max value). -/
  confirmation_byzantine_threshold : ℕ
  /-- The spec's "Max. Value" column: `uint64(25)`. (Also keeps the
      `100 - CONFIRMATION_BYZANTINE_THRESHOLD` subtraction in
      `compute_honest_ffg_support_for_current_target` non-truncating.) -/
  confirmation_byzantine_threshold_le : confirmation_byzantine_threshold ≤ 25
  /-- `COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR` (FCR constant, per
      mille; `5`). -/
  committee_weight_estimation_adjustment_factor : ℕ
  /-- `EFFECTIVE_BALANCE_INCREMENT` (preset, Gwei; mainnet `10^9`). -/
  effective_balance_increment : ℕ
  /-- Effective-balance quantization is nonzero (phase0 preset invariant). -/
  effective_balance_increment_pos : 0 < effective_balance_increment
  /-- The executable FCR divides Gwei estimates by `100`; phase0 effective
      balances are quantized finely enough that real validator-set weights have
      no sub-`100` rounding residue. -/
  hundred_dvd_effective_balance_increment : 100 ∣ effective_balance_increment
  /-- `ATTESTATION_DUE_BPS` (config, basis points of `SLOT_DURATION_MS`;
      mainnet `3333`). -/
  attestation_due_bps : ℕ
  /-- `MIN_SEED_LOOKAHEAD` (preset, epochs; mainnet `1`). -/
  min_seed_lookahead : ℕ

/-- The mainnet values of every constant the FCR reads (consensus-specs
`presets/mainnet/phase0.yaml` + `configs/mainnet.yaml` +
`fast-confirmation.md` tables). -/
def mainnet_config : Config where
  slots_per_epoch := 32
  slots_per_epoch_pos := by decide
  slot_duration_ms := 12000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 40
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 1000000000
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 3333
  min_seed_lookahead := 1

/-- `GENESIS_SLOT` (phase0 beacon-chain constant). -/
def GENESIS_SLOT : ℕ := 0

/-- `GENESIS_EPOCH` (phase0 beacon-chain constant). -/
def GENESIS_EPOCH : ℕ := 0

/-- `BASIS_POINTS` (fork-choice constant): `uint64(10000)`. -/
def BASIS_POINTS : ℕ := 10000

/-- `UINT64_MAX` (used by `seconds_to_milliseconds`'s overflow guard, which is
transcribed literally even though the `ℕ` model cannot overflow). -/
def UINT64_MAX : ℕ := 2 ^ 64 - 1

/-- Phase0 `FAR_FUTURE_EPOCH`. In the executable specification this is the
largest `uint64`; in the `ℕ` transcription it remains a finite sentinel. Proofs
about concrete executions must therefore carry an explicit horizon no greater
than this value instead of treating the sentinel as mathematical infinity. -/
def FAR_FUTURE_EPOCH : ℕ := UINT64_MAX

/-- Every epoch-sized interval which starts in the `uint64` slot range ends
in that range. Phase0 presets satisfy this because `SLOTS_PER_EPOCH` divides
`2^64 = UINT64_MAX + 1`. -/
def EpochEndsFitUint64 (cfg : Config) : Prop :=
  cfg.slots_per_epoch ∣ UINT64_MAX + 1

theorem mainnet_epochEndsFitUint64 : EpochEndsFitUint64 mainnet_config := by
  refine ⟨2 ^ 59, ?_⟩
  norm_num [EpochEndsFitUint64, UINT64_MAX, mainnet_config]

end FastConfirmation.Spec

import YesMetaZFC.SetTheory.InnerModel.ProofCode.Parser.Correctness

/-! # 在实际候选集合上判定码名合法性

正反证书计算同一个 rud 闭包和同一个语法层，再分别验证成员条件及其否定。
两次计算的唯一性使反向证书可信；不以“找不到合法证书”定义否定。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pg_wit_d (T n Y W : M.Domain) : Prop :=
  (rc_value_s pg_op_s).matrix_binary.toBinarySchema.denote ((rd_seed_env_l T).push n) Y W
def pg_wit_m {n} (T h Y W : Term n) : Formula 1 n := (rc_value_s pg_op_s).matrix_m (fun _ => T) h Y W
derive_free_closed pg_wit_m
theorem pg_wit_sat_l {n} (ρ : Env M n) (T h Y W : Term n) :
    Formula.satisfies ρ (pg_wit_m T h Y W) ↔ Pg_wit_d (T.eval ρ) (h.eval ρ) (Y.eval ρ) (W.eval ρ) := by
  rw [pg_wit_m, S1_binary.matrix_sat_l]
  exact Formula.closed_env_l _ (rc_value_s pg_op_s).matrix.freeClosed rfl
theorem pg_wit_value_l (hE : Extensional M) (T n Y : M.Domain) : (∃ W, Pg_wit_d T n Y W) ↔ Pg_level_d T n Y :=
  ((rc_value_s pg_op_s).sat_l (rd_seed_env_l T) n Y).symm.trans (rc_value_sat_l hE pg_op_s (rd_seed_env_l T) n Y)

def Pg_bit_d (b : Bool) (P : Prop) : Prop := match b with | false => P | true => ¬ P
def pg_bit_m {n} (b : Bool) (φ : Formula 1 n) : Formula 1 n := match b with | false => φ | true => .neg φ
@[simp] theorem pg_bit_closed_l {n} (b : Bool) (φ : Formula 1 n) (hc : φ.FreeClosed) : (pg_bit_m b φ).FreeClosed := by
  cases b
  · exact hc
  · simpa only [pg_bit_m, Definitional.Formula.FreeClosed] using hc
theorem pg_bit_delta_l {n} (b : Bool) (φ : Formula 1 n) (hd : φ.IsDelta0) : (pg_bit_m b φ).IsDelta0 := by
  cases b; exact hd; exact .neg hd
theorem pg_bit_sat_l {n} (b : Bool) (ρ : Env M n) (φ : Formula 1 n) :
    Formula.satisfies ρ (pg_bit_m b φ) ↔ Pg_bit_d b (Formula.satisfies ρ φ) := by
  cases b
  · rfl
  · exact Formula.satisfies_neg_iff _ _
theorem pg_bit_congr_l {P Q : Prop} (b : Bool) (h : P ↔ Q) : Pg_bit_d b P ↔ Pg_bit_d b Q := by
  cases b
  · exact h
  · exact ⟨fun hn hq => hn (h.mpr hq), fun hn hp => hn (h.mp hp)⟩

def Pg_dec_d (b : Bool) (T v : M.Domain) : Prop := ∃ a n c R Y,
  Rd_triple_d v a n c ∧ M.IsOrdinal a ∧ KP.N0_d n ∧ Rd_closure_d a R ∧ Pg_level_d T n Y ∧
    Pg_bit_d b (M.mem c R ∧ M.mem c Y)
def pg_dec_s (b : Bool) : Delta0BinarySchema 1 where
  body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
    Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <|
      .conj (rd_triple0_m (.bound 8) (.bound 6) (.bound 5) (.bound 4)) <|
        .conj (KP.ord0_m (.bound 6)) <| .conj (KP.n0_m (.bound 5)) <|
          .conj (rd_closure_s.matrix_m Fin.elim0 (.bound 6) (.bound 3) (.bound 1)) <|
            .conj (pg_wit_m (.bound 9) (.bound 5) (.bound 2) .newest)
              (pg_bit_m b (.conj (.mem (.bound 4) (.bound 3)) (.mem (.bound 4) (.bound 2))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (rd_triple0_delta_l ..) (.conj (KP.ord0_delta_l _) (.conj (KP.n0_delta_l _)
      (.conj (rd_closure_s.matrix.delta0.bind_l _) (.conj ((rc_value_s pg_op_s).matrix.delta0.bind_l _)
        (pg_bit_delta_l _ _ (.conj (.mem _ _) (.mem _ _))))))))))))))

theorem pg_dec_sat_l (hKP : M.Models KP) (b : Bool) (ρ : Env M 1) (v : M.Domain) :
    (∃ K, (pg_dec_s b).toBinarySchema.denote ρ v K) ↔ Pg_dec_d b (ρ.bound 0) v := by
  simp only [BinarySchema.denote, pg_dec_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hKP.1, KP.ord0_sat_l hKP, KP.n0_sat_l hKP.1, po_matrix_env_l rd_closure_s (jh_env_l v),
    pg_wit_sat_l, pg_bit_sat_l, Formula.satisfies_mem_iff]
  change (∃ K a, M.mem a K ∧ ∃ n, M.mem n K ∧ ∃ c, M.mem c K ∧ ∃ R, M.mem R K ∧ ∃ Y, M.mem Y K ∧
    ∃ W, M.mem W K ∧ ∃ V, M.mem V K ∧ Rd_triple_d v a n c ∧ M.IsOrdinal a ∧ KP.N0_d n ∧
      rd_closure_s.matrix_binary.toBinarySchema.denote ((jh_env_l v).push a) R W ∧
        Pg_wit_d (ρ.bound 0) n Y V ∧ Pg_bit_d b (M.mem c R ∧ M.mem c Y)) ↔ _
  constructor
  · rintro ⟨K, a, _, n, _, c, _, R, _, Y, _, W, _, V, _, hv, ha, hn, hr, hy, hc⟩
    exact ⟨a, n, c, R, Y, hv, ha, hn,
      (rd_closure_sat_l hKP.1 _ a R).mp ((rd_closure_s.sat_l _ a R).mpr ⟨W, hr⟩),
        (pg_wit_value_l hKP.1 _ _ _).mp ⟨V, hy⟩, hc⟩
  · rintro ⟨a, n, c, R, Y, hv, ha, hn, hr, hy, hc⟩
    obtain ⟨W, hr⟩ := (rd_closure_s.sat_l (jh_env_l v) a R).mp ((rd_closure_sat_l hKP.1 _ a R).mpr hr)
    obtain ⟨V, hy⟩ := (pg_wit_value_l hKP.1 _ _ _).mpr hy
    obtain ⟨K, hk⟩ := kp_finite_cover_l hKP [a, n, c, R, Y, W, V]
    exact ⟨K, a, (hk a (by simp)).2, n, (hk n (by simp)).2, c, (hk c (by simp)).2, R, (hk R (by simp)).2,
      Y, (hk Y (by simp)).2, W, (hk W (by simp)).2, V, (hk V (by simp)).2, hv, ha, hn, hr, hy, hc⟩

theorem pg_dec_correct_l (hM : M.Models KPi) (b : Bool) {T v a n c : M.Domain} (ht : M.TransitiveSet T)
    (hv : Rd_triple_d v a n c) (ha : M.IsOrdinal a) (hn : KP.N0_d n) (hc : M.mem c T) :
    Pg_dec_d b T v ↔ Pg_bit_d b (Pn_valid_d v) := by
  have spec {R Y} (hr : Rd_closure_d a R) (hy : Pg_level_d T n Y) :
      Pn_valid_d v ↔ M.mem c R ∧ M.mem c Y := by
    constructor
    · rintro ⟨a', n', c', hv', ha', hn', hh, C, hC, hcC⟩
      obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hv' hv
      have he := rd_closure_unique_l hM hC hr; subst C
      exact ⟨hcC, (pg_level_height_l hM ht hn hy _).mpr ⟨hc, hh⟩⟩
    · rintro ⟨hcR, hcY⟩
      exact ⟨a, n, c, hv, ha, hn, ((pg_level_height_l hM ht hn hy c).mp hcY).2, R, hr, hcR⟩
  constructor
  · rintro ⟨a', n', c', R, Y, hv', _, _, hr, hy, hd⟩
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hv' hv
    exact (pg_bit_congr_l b (spec hr hy).symm).mp hd
  · intro hd
    obtain ⟨R, hr⟩ := rd_closure_exists_l hM a
    obtain ⟨Y, hy⟩ := pg_level_exists_l hM T n
    exact ⟨a, n, c, R, Y, hv, ha, hn, hr, hy, (pg_bit_congr_l b (spec hr hy)).mp hd⟩

def pg_filter_s : S1_binary 1 := S1_binary.separate (pg_dec_s false) (pg_dec_s true)
theorem pg_filter_sat_l (hM : M.Models KPi) {T B D : M.Domain} (ht : M.TransitiveSet T)
    (hb : ∀ v, M.mem v B → ∃ a n c, Rd_triple_d v a n c ∧ M.IsOrdinal a ∧ KP.N0_d n ∧ M.mem c T) :
    pg_filter_s.schema.denote (rd_seed_env_l T) B D ↔ ∀ v, M.mem v D ↔ M.mem v B ∧ Pn_valid_d v := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have correct b v (hv : M.mem v B) : (∃ W, (pg_dec_s b).toBinarySchema.denote (rd_seed_env_l T) v W) ↔ Pg_bit_d b (Pn_valid_d v) := by
    obtain ⟨a, n, c, hp, ha, hn, hc⟩ := hb v hv
    exact (pg_dec_sat_l hKP b _ v).trans (pg_dec_correct_l hM b ht hp ha hn hc)
  rw [pg_filter_s, S1_binary.separate_sat_l hKP _ _ _ _ _ (fun v hv => by
    rw [correct false v hv, correct true v hv]; exact ⟨fun h hn => hn h, Classical.not_not.mp⟩)]
  exact forall_congr' fun v => iff_congr Iff.rfl (and_congr_right fun hv => correct false v hv)

theorem pg_filter_exists_l (hM : M.Models KPi) {T B : M.Domain} (ht : M.TransitiveSet T)
    (hb : ∀ v, M.mem v B → ∃ a n c, Rd_triple_d v a n c ∧ M.IsOrdinal a ∧ KP.N0_d n ∧ M.mem c T) :
    ∃ D, pg_filter_s.schema.denote (rd_seed_env_l T) B D := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have correct b v (hv : M.mem v B) : (∃ W, (pg_dec_s b).toBinarySchema.denote (rd_seed_env_l T) v W) ↔ Pg_bit_d b (Pn_valid_d v) := by
    obtain ⟨a, n, c, hp, ha, hn, hc⟩ := hb v hv
    exact (pg_dec_sat_l hKP b _ v).trans (pg_dec_correct_l hM b ht hp ha hn hc)
  obtain ⟨D, hd⟩ := KP.d1_separation_l hKP (pg_dec_s false) (pg_dec_s true) (rd_seed_env_l T) B (fun v hv => by
    rw [correct false v hv, correct true v hv]; exact ⟨fun h hn => hn h, Classical.not_not.mp⟩)
  exact ⟨D, (pg_filter_sat_l hM ht hb).mpr (fun v => (hd v).trans (and_congr_right fun hv => correct false v hv))⟩

end YesMetaZFC.SetTheory.InnerModel

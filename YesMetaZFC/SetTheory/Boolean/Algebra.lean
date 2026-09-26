import YesMetaZFC.SetTheory.Boolean.Completion

/-! # 内部布尔代数及切割的有限运算

用集合编码序和运算的图关系陈述布尔代数律。运算的存在量词始终留在命题中，
不从唯一存在的模型对象选出宿主函数。切割的交与剩余仍用纯公式分离构造。
-/

namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project FilterZF
universe u
variable {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}

def Meet_d (𝕀 : 𝒞.Interpretation ℳ) (B R a b c : ℳ.Domain) : Prop :=
  ℳ.mem c B ∧ ∀ d, ℳ.mem d B →
    (ℳ.PairMember 𝕀 d c R ↔ ℳ.PairMember 𝕀 d a R ∧ ℳ.PairMember 𝕀 d b R)

def Imp_d (𝕀 : 𝒞.Interpretation ℳ) (B R a b c : ℳ.Domain) : Prop :=
  ℳ.mem c B ∧ ∀ d, ℳ.mem d B →
    (ℳ.PairMember 𝕀 d c R ↔ ∀ m, Meet_d 𝕀 B R d a m → ℳ.PairMember 𝕀 m b R)

/-- 关系版本与宿主 `BA_alg` 采用相同的剩余及双重否定公理。 -/
structure Boolean_d (𝕀 : 𝒞.Interpretation ℳ) (B R z : ℳ.Domain) : Prop where
  order : Order_d 𝕀 B R
  bot_mem : ℳ.mem z B
  bot_le : ∀ a, ℳ.mem a B → ℳ.PairMember 𝕀 z a R
  meet : ∀ a b, ℳ.mem a B → ℳ.mem b B → ∃ c, Meet_d 𝕀 B R a b c
  imp : ∀ a b, ℳ.mem a B → ℳ.mem b B → ∃ c, Imp_d 𝕀 B R a b c
  double_neg : ∀ a b c, ℳ.mem a B → Imp_d 𝕀 B R a z b → Imp_d 𝕀 B R b z c → c = a

theorem meet_bounds_d (𝕀 : 𝒞.Interpretation ℳ) {B R a b c : ℳ.Domain}
    (hR : Order_d 𝕀 B R) (h : Meet_d 𝕀 B R a b c) :
    ℳ.PairMember 𝕀 c a R ∧ ℳ.PairMember 𝕀 c b R := (h.2 c h.1).mp (hR.refl c h.1)

theorem meet_comm_d (𝕀 : 𝒞.Interpretation ℳ) {B R a b c : ℳ.Domain}
    (h : Meet_d 𝕀 B R a b c) : Meet_d 𝕀 B R b a c :=
  ⟨h.1, fun d hd => (h.2 d hd).trans and_comm⟩

theorem meet_self_d (𝕀 : 𝒞.Interpretation ℳ) {B R a : ℳ.Domain}
    (h : ℳ.mem a B) : Meet_d 𝕀 B R a a a :=
  ⟨h, fun _ _ => ⟨fun k => ⟨k, k⟩, fun k => k.1⟩⟩

def meet_m (𝒞 : OrderedPairConvention) {n : Nat} (B R a b c : Term n) : Formula 1 n :=
  .conj (.mem c B) (.forallE (.imp (.mem .newest B.weaken)
    (.iff (Formula.orderedPairMem 𝒞 .newest c.weaken R.weaken)
      (.conj (Formula.orderedPairMem 𝒞 .newest a.weaken R.weaken)
        (Formula.orderedPairMem 𝒞 .newest b.weaken R.weaken)))))

derive_free_closed meet_m

theorem meet_sat_d (𝕀 : 𝒞.Interpretation ℳ) {n : Nat} (e : Env ℳ n)
    (B R a b c : Term n) : Formula.satisfies e (meet_m 𝒞 B R a b c) ↔
      Meet_d 𝕀 (B.eval e) (R.eval e) (a.eval e) (b.eval e) (c.eval e) := by
  simp only [meet_m, Meet_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]

def ImpCut_d (𝕀 : 𝒞.Interpretation ℳ) (B R I J a : ℳ.Domain) : Prop :=
  ∀ b, ℳ.mem b I → ∀ c, Meet_d 𝕀 B R a b c → ℳ.mem c J

def imp_cut_m (𝒞 : OrderedPairConvention) : UnarySchema 4 where
  body := .forallE (.imp (.mem (.bound 0) (.bound 3)) (.forallE (.imp
    (meet_m 𝒞 (.bound 6) (.bound 5) (.bound 2) (.bound 1) (.bound 0))
    (.mem (.bound 0) (.bound 3)))))

theorem meet_cut_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    {B R I J : ℳ.Domain} (hI : Cut_d 𝕀 B R I) (hJ : Cut_d 𝕀 B R J) :
    ∃ K, Cut_d 𝕀 B R K ∧ ∀ a, ℳ.mem a K ↔ ℳ.mem a I ∧ ℳ.mem a J := by
  obtain ⟨K, hK⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) I J
  refine ⟨K, ⟨fun a ha => hI.1 a ((hK a).mp ha).1, ?_⟩, hK⟩
  intro a ha h
  exact (hK a).mpr ⟨hI.2 a ha (fun b hb k => h b hb (fun c hc => k c ((hK c).mp hc).1)),
    hJ.2 a ha (fun b hb k => h b hb (fun c hc => k c ((hK c).mp hc).2))⟩

theorem imp_cut_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    {B R z I J : ℳ.Domain} (hB : Boolean_d 𝕀 B R z)
    (hI : Cut_d 𝕀 B R I) (hJ : Cut_d 𝕀 B R J) :
    ∃ K, Cut_d 𝕀 B R K ∧ ∀ a, ℳ.mem a K ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R I J a := by
  let e : Env ℳ 4 := ⟨fun i => if i = 0 then J else if i = 1 then I else
    if i = 2 then R else B, fun _ => B⟩
  obtain ⟨K, hK⟩ := ZF.separation_exists_d hZF (imp_cut_m 𝒞) e B
  have h : ∀ a, ℳ.mem a K ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R I J a := by
    intro a
    rw [hK]
    simp only [imp_cut_m, ImpCut_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, meet_sat_d 𝕀, Term.eval_bound]
    rfl
  refine ⟨K, ⟨fun a ha => ((h a).mp ha).1, ?_⟩, h⟩
  intro a ha k
  refine (h a).mpr ⟨ha, fun b hb m hm => hJ.2 m hm.1 ?_⟩
  intro c hc hJc
  obtain ⟨q, hq⟩ := hB.imp b c (hI.1 b hb) hc
  have haq : ℳ.PairMember 𝕀 a q R := k q hq.1 (fun d hd =>
    (hq.2 d ((h d).mp hd).1).mpr (fun v hv => hJc v (((h d).mp hd).2 b hb v hv)))
  exact (hq.2 a ha).mp haq m hm

theorem residuation_d (𝕀 : 𝒞.Interpretation ℳ)
    {B R I J K L H : ℳ.Domain} (hR : Order_d 𝕀 B R)
    (hI : Cut_d 𝕀 B R I) (hL : Cut_d 𝕀 B R L)
    (hK : ∀ a, ℳ.mem a K ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R I J a)
    (hH : ∀ a, ℳ.mem a H ↔ ℳ.mem a L ∧ ℳ.mem a I) :
    Subset_d (ℳ := ℳ) L K ↔ Subset_d (ℳ := ℳ) H J := by
  constructor
  · intro h a ha
    obtain ⟨haL, haI⟩ := (hH a).mp ha
    exact ((hK a).mp (h a haL)).2 a haI a (meet_self_d 𝕀 (hL.1 a haL))
  · intro h a ha
    refine (hK a).mpr ⟨hL.1 a ha, fun b hb m hm => ?_⟩
    obtain ⟨hma, hmb⟩ := meet_bounds_d 𝕀 hR hm
    exact h m ((hH m).mpr ⟨cut_lower_d 𝕀 hR hL hm.1 ha hma,
      cut_lower_d 𝕀 hR hI hm.1 hb hmb⟩)

theorem double_neg_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    {B R z I Z K H : ℳ.Domain} (hB : Boolean_d 𝕀 B R z) (hI : Cut_d 𝕀 B R I)
    (hZ : ∀ a, ℳ.mem a Z ↔ ℳ.mem a B ∧ ℳ.PairMember 𝕀 a z R)
    (hK : ∀ a, ℳ.mem a K ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R I Z a)
    (hH : ∀ a, ℳ.mem a H ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R K Z a) : H = I := by
  apply hZF.1.eq_of_same_members
  intro a
  constructor
  · intro ha
    obtain ⟨haB, haK⟩ := (hH a).mp ha
    apply hI.2 a haB
    intro b hb hIb
    obtain ⟨n, hn⟩ := hB.imp b z hb hB.bot_mem
    obtain ⟨q, hq⟩ := hB.imp n z hn.1 hB.bot_mem
    have hqb := hB.double_neg b n q hb hn hq
    have hnK : ℳ.mem n K := by
      refine (hK n).mpr ⟨hn.1, fun c hc m hm => (hZ m).mpr ⟨hm.1, ?_⟩⟩
      obtain ⟨d, hd⟩ := hB.meet n b hn.1 hb
      have hdz := (hn.2 n hn.1).mp (hB.order.refl n hn.1) d hd
      obtain ⟨hmn, hmc⟩ := meet_bounds_d 𝕀 hB.order hm
      have hmd := (hd.2 m hm.1).mpr ⟨hmn,
        hB.order.trans m c b hm.1 (hI.1 c hc) hb hmc (hIb c hc)⟩
      exact hB.order.trans m d z hm.1 hd.1 hB.bot_mem hmd hdz
    have haq := (hq.2 a haB).mpr (fun m hm => ((hZ m).mp (haK n hnK m hm)).2)
    exact hqb ▸ haq
  · intro ha
    exact (hH a).mpr ⟨hI.1 a ha, fun n hn m hm =>
      ((hK n).mp hn).2 a ha m (meet_comm_d 𝕀 hm)⟩

/-- 内部完备化的具体载体、零元与运算规格；不是预设存在的完备模型。 -/
structure Completion_d (𝕀 : 𝒞.Interpretation ℳ) (B R z K Z : ℳ.Domain) : Prop where
  carrier : ∀ I, ℳ.mem I K ↔ Cut_d 𝕀 B R I
  zero : ℳ.mem Z K ∧ ∀ a, ℳ.mem a Z ↔ ℳ.mem a B ∧ ℳ.PairMember 𝕀 a z R
  bot_le : ∀ I, ℳ.mem I K → Subset_d (ℳ := ℳ) Z I
  sup : ∀ S, Subset_d (ℳ := ℳ) S K → ∃ J, ℳ.mem J K ∧
    (∀ I, ℳ.mem I S → Subset_d (ℳ := ℳ) I J) ∧
    ∀ L, ℳ.mem L K → (∀ I, ℳ.mem I S → Subset_d (ℳ := ℳ) I L) → Subset_d (ℳ := ℳ) J L
  meet : ∀ I J, ℳ.mem I K → ℳ.mem J K → ∃ H, ℳ.mem H K ∧
    ∀ a, ℳ.mem a H ↔ ℳ.mem a I ∧ ℳ.mem a J
  imp : ∀ I J, ℳ.mem I K → ℳ.mem J K → ∃ H, ℳ.mem H K ∧
    ∀ a, ℳ.mem a H ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R I J a
  residual : ∀ I J H L M, ℳ.mem I K → ℳ.mem L K →
    (∀ a, ℳ.mem a H ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R I J a) →
    (∀ a, ℳ.mem a M ↔ ℳ.mem a L ∧ ℳ.mem a I) →
    (Subset_d (ℳ := ℳ) L H ↔ Subset_d (ℳ := ℳ) M J)
  involutive : ∀ I H L, ℳ.mem I K →
    (∀ a, ℳ.mem a H ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R I Z a) →
    (∀ a, ℳ.mem a L ↔ ℳ.mem a B ∧ ImpCut_d 𝕀 B R H Z a) → L = I

/-- ZF 中实际构造完备布尔代数的载体与零元；其余运算以唯一图规格使用。 -/
theorem boolean_completion_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    {B R z : ℳ.Domain} (hB : Boolean_d 𝕀 B R z) :
    ∃ K Z, Completion_d 𝕀 B R z K Z := by
  obtain ⟨K, hK⟩ := completion_exists_d 𝕀 hZF B R
  obtain ⟨Z, hZ, hz⟩ := principal_exists_d 𝕀 hZF hB.bot_mem
  refine ⟨K, Z, ⟨hK, ⟨(hK Z).mpr hZ, hz⟩, ?_,
    sup_exists_d 𝕀 hZF hK, ?_, ?_, ?_, ?_⟩⟩
  · intro I hI a ha
    obtain ⟨haB, haz⟩ := (hz a).mp ha
    apply ((hK I).mp hI).2 a haB
    exact fun b hb _ => hB.order.trans a z b haB hB.bot_mem hb haz (hB.bot_le b hb)
  · intro I J hI hJ
    obtain ⟨H, hH, h⟩ := meet_cut_exists_d 𝕀 hZF ((hK I).mp hI) ((hK J).mp hJ)
    exact ⟨H, (hK H).mpr hH, h⟩
  · intro I J hI hJ
    obtain ⟨H, hH, h⟩ := imp_cut_exists_d 𝕀 hZF hB ((hK I).mp hI) ((hK J).mp hJ)
    exact ⟨H, (hK H).mpr hH, h⟩
  · intro I J H L M hI hL hh hm
    exact residuation_d 𝕀 hB.order ((hK I).mp hI) ((hK L).mp hL) hh hm
  · intro I H L hI hh hl
    exact double_neg_d 𝕀 hZF hB ((hK I).mp hI) hz hh hl

/-- 任意切割中的每个元素都由位于该切割之下的主切割覆盖。 -/
theorem principal_dense_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    {B R I : ℳ.Domain} (hR : Order_d 𝕀 B R) (hI : Cut_d 𝕀 B R I)
    {a : ℳ.Domain} (ha : ℳ.mem a I) :
    ∃ P, Cut_d 𝕀 B R P ∧ ℳ.mem a P ∧ Subset_d (ℳ := ℳ) P I ∧
      ∀ b, ℳ.mem b P ↔ ℳ.mem b B ∧ ℳ.PairMember 𝕀 b a R := by
  obtain ⟨P, hP, h⟩ := principal_exists_d 𝕀 hZF (hI.1 a ha)
  exact ⟨P, hP, (h a).mpr ⟨hI.1 a ha, hR.refl a (hI.1 a ha)⟩,
    fun b hb => cut_lower_d 𝕀 hR hI ((h b).mp hb).1 ha ((h b).mp hb).2, h⟩

theorem principal_injective_d (𝕀 : 𝒞.Interpretation ℳ) {B R a b I J : ℳ.Domain}
    (hR : Order_d 𝕀 B R) (ha : ℳ.mem a B) (hb : ℳ.mem b B)
    (hI : ∀ c, ℳ.mem c I ↔ ℳ.mem c B ∧ ℳ.PairMember 𝕀 c a R)
    (hJ : ∀ c, ℳ.mem c J ↔ ℳ.mem c B ∧ ℳ.PairMember 𝕀 c b R)
    (h : I = J) : a = b := by
  subst J
  exact hR.antisymm a b ha hb
    ((principal_order_d 𝕀 hR ha hb hI hJ).mp (fun _ k => k))
    ((principal_order_d 𝕀 hR hb ha hJ hI).mp (fun _ k => k))

theorem principal_meet_d (𝕀 : 𝒞.Interpretation ℳ) {B R a b c I J K : ℳ.Domain}
    (h : Meet_d 𝕀 B R a b c)
    (hI : ∀ d, ℳ.mem d I ↔ ℳ.mem d B ∧ ℳ.PairMember 𝕀 d a R)
    (hJ : ∀ d, ℳ.mem d J ↔ ℳ.mem d B ∧ ℳ.PairMember 𝕀 d b R)
    (hK : ∀ d, ℳ.mem d K ↔ ℳ.mem d B ∧ ℳ.PairMember 𝕀 d c R) :
    ∀ d, ℳ.mem d K ↔ ℳ.mem d I ∧ ℳ.mem d J := by
  intro d
  constructor
  · intro hd
    obtain ⟨hdB, hdc⟩ := (hK d).mp hd
    obtain ⟨hda, hdb⟩ := (h.2 d hdB).mp hdc
    exact ⟨(hI d).mpr ⟨hdB, hda⟩, (hJ d).mpr ⟨hdB, hdb⟩⟩
  · rintro ⟨hdI, hdJ⟩
    obtain ⟨hdB, hda⟩ := (hI d).mp hdI
    exact (hK d).mpr ⟨hdB, (h.2 d hdB).mpr ⟨hda, ((hJ d).mp hdJ).2⟩⟩

theorem principal_imp_d (𝕀 : 𝒞.Interpretation ℳ) {B R z a b c I J K : ℳ.Domain}
    (hB : Boolean_d 𝕀 B R z) (ha : ℳ.mem a B) (hb : ℳ.mem b B)
    (h : Imp_d 𝕀 B R a b c)
    (hI : ∀ d, ℳ.mem d I ↔ ℳ.mem d B ∧ ℳ.PairMember 𝕀 d a R)
    (hJ : ∀ d, ℳ.mem d J ↔ ℳ.mem d B ∧ ℳ.PairMember 𝕀 d b R)
    (hK : ∀ d, ℳ.mem d K ↔ ℳ.mem d B ∧ ℳ.PairMember 𝕀 d c R) :
    ∀ d, ℳ.mem d K ↔ ℳ.mem d B ∧ ImpCut_d 𝕀 B R I J d := by
  intro d
  constructor
  · intro hd
    obtain ⟨hdB, hdc⟩ := (hK d).mp hd
    refine ⟨hdB, fun e he m hm => (hJ m).mpr ⟨hm.1, ?_⟩⟩
    obtain ⟨q, hq⟩ := hB.meet d a hdB ha
    have hqb := (h.2 d hdB).mp hdc q hq
    obtain ⟨hmd, hme⟩ := meet_bounds_d 𝕀 hB.order hm
    have hmq := (hq.2 m hm.1).mpr ⟨hmd,
      hB.order.trans m e a hm.1 ((hI e).mp he).1 ha hme ((hI e).mp he).2⟩
    exact hB.order.trans m q b hm.1 hq.1 hb hmq hqb
  · rintro ⟨hd, hdI⟩
    exact (hK d).mpr ⟨hd, (h.2 d hd).mpr (fun m hm =>
      ((hJ m).mp (hdI a ((hI a).mpr ⟨ha, hB.order.refl a ha⟩) m hm)).2)⟩

end YesMetaZFC.SetTheory.BooleanZF

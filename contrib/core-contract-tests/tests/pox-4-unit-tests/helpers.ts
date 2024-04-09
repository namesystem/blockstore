import {
  getPublicKeyFromPrivate,
  publicKeyToBtcAddress,
} from "@stacks/encryption";
import { StacksDevnet } from "@stacks/network";
import {
  Pox4SignatureTopic,
  StackingClient,
  poxAddressToTuple,
} from "@stacks/stacking";
import {
  Cl,
  StacksPrivateKey,
  TransactionVersion,
  UIntCV,
  createStacksPrivateKey,
  getAddressFromPrivateKey,
} from "@stacks/transactions";

export const POX_DEPLOYER = "ST000000000000000000002AMW42H";
export const POX_CONTRACT = `${POX_DEPLOYER}.pox-4`;

// Error codes from the contract
export const ERRORS = {
  ERR_STACKING_UNREACHABLE: 255,
  ERR_STACKING_CORRUPTED_STATE: 254,
  ERR_STACKING_INSUFFICIENT_FUNDS: 1,
  ERR_STACKING_INVALID_LOCK_PERIOD: 2,
  ERR_STACKING_ALREADY_STACKED: 3,
  ERR_STACKING_NO_SUCH_PRINCIPAL: 4,
  ERR_STACKING_EXPIRED: 5,
  ERR_STACKING_STX_LOCKED: 6,
  ERR_STACKING_PERMISSION_DENIED: 9,
  ERR_STACKING_THRESHOLD_NOT_MET: 11,
  ERR_STACKING_POX_ADDRESS_IN_USE: 12,
  ERR_STACKING_INVALID_POX_ADDRESS: 13,
  ERR_STACKING_INVALID_AMOUNT: 18,
  ERR_NOT_ALLOWED: 19,
  ERR_STACKING_ALREADY_DELEGATED: 20,
  ERR_DELEGATION_EXPIRES_DURING_LOCK: 21,
  ERR_DELEGATION_TOO_MUCH_LOCKED: 22,
  ERR_DELEGATION_POX_ADDR_REQUIRED: 23,
  ERR_INVALID_START_BURN_HEIGHT: 24,
  ERR_NOT_CURRENT_STACKER: 25,
  ERR_STACK_EXTEND_NOT_LOCKED: 26,
  ERR_STACK_INCREASE_NOT_LOCKED: 27,
  ERR_DELEGATION_NO_REWARD_SLOT: 28,
  ERR_DELEGATION_WRONG_REWARD_SLOT: 29,
  ERR_STACKING_IS_DELEGATED: 30,
  ERR_STACKING_NOT_DELEGATED: 31,
  ERR_INVALID_SIGNER_KEY: 32,
  ERR_REUSED_SIGNER_KEY: 33,
  ERR_DELEGATION_ALREADY_REVOKED: 34,
  ERR_INVALID_SIGNATURE_PUBKEY: 35,
  ERR_INVALID_SIGNATURE_RECOVER: 36,
  ERR_INVALID_REWARD_CYCLE: 37,
  ERR_SIGNER_AUTH_AMOUNT_TOO_HIGH: 38,
  ERR_SIGNER_AUTH_USED: 39,
  ERR_INVALID_INCREASE: 40,
};

// Keys to use for stacking
// wallet_1, wallet_2, wallet_3 private keys
const stackingKeys = [
  "7287ba251d44a4d3fd9276c88ce34c5c52a038955511cccaf77e61068649c17801",
  "530d9f61984c888536871c6573073bdfc0058896dc1adfe9a6a10dfacadc209101",
  "d655b2523bcd65e34889725c73064feb17ceb796831c0e111ba1a552b0f31b3901",
];

export type StackerInfo = {
  authId: number;
  privKey: string;
  pubKey: string;
  stxAddress: string;
  btcAddr: string;
  signerPrivKey: StacksPrivateKey;
  signerPubKey: string;
  client: StackingClient;
};

export const stackers = Object.freeze(
  stackingKeys.map((privKey, i) => {
    const network = new StacksDevnet();

    const pubKey = getPublicKeyFromPrivate(privKey);
    const stxAddress = getAddressFromPrivateKey(
      privKey,
      TransactionVersion.Testnet
    );
    const signerPrivKey = createStacksPrivateKey(privKey);
    const signerPubKey = getPublicKeyFromPrivate(signerPrivKey.data);

    const info: StackerInfo = {
      authId: i,
      privKey,
      pubKey,
      stxAddress,
      btcAddr: publicKeyToBtcAddress(pubKey),
      signerPrivKey: signerPrivKey,
      signerPubKey: signerPubKey,
      client: new StackingClient(stxAddress, network),
    };
    return info;
  })
);

const getPoxInfo = () => {
  const poxInfo = simnet.callReadOnlyFn(
    POX_CONTRACT,
    "get-pox-info",
    [],
    simnet.deployer
  );
  // @ts-ignore
  const data = poxInfo.result.value.data;
  const typedPoxInfo = {
    firstBurnchainBlockHeight: data["first-burnchain-block-height"]
      .value as bigint,
    minAmountUstx: data["min-amount-ustx"].value as bigint,
    prepareCycleLength: data["prepare-cycle-length"].value as bigint,
    rewardCycleId: data["reward-cycle-id"].value as bigint,
    rewardCycleLength: data["reward-cycle-length"].value as bigint,
    totalLiquidSupplyUstx: data["total-liquid-supply-ustx"].value as bigint,
  };

  return typedPoxInfo;
};

export const getStackingMinimum = () => {
  const response = simnet.callReadOnlyFn(
    POX_CONTRACT,
    "get-stacking-minimum",
    [],
    simnet.deployer
  );
  return Number((response.result as UIntCV).value);
};

export const burnHeightToRewardCycle = (burnHeight: number) => {
  const poxInfo = getPoxInfo();
  return Number(
    (BigInt(burnHeight) - poxInfo.firstBurnchainBlockHeight) /
      poxInfo.rewardCycleLength
  );
};

export const stackStx = (
  stacker: StackerInfo,
  amount: number,
  startBurnHeight: number,
  lockPeriod: number,
  maxAmount: number,
  authId: number,
  sender: string
) => {
  const rewardCycle = burnHeightToRewardCycle(startBurnHeight);
  const sigArgs = {
    authId,
    maxAmount,
    rewardCycle,
    period: lockPeriod,
    topic: Pox4SignatureTopic.StackStx,
    poxAddress: stacker.btcAddr,
    signerPrivateKey: stacker.signerPrivKey,
  };
  const signerSignature = stacker.client.signPoxSignature(sigArgs);
  const signerKey = Cl.bufferFromHex(stacker.signerPubKey);

  const stackStxArgs = [
    Cl.uint(amount),
    poxAddressToTuple(stacker.btcAddr),
    Cl.uint(startBurnHeight),
    Cl.uint(lockPeriod),
    Cl.some(Cl.bufferFromHex(signerSignature)),
    signerKey,
    Cl.uint(maxAmount),
    Cl.uint(authId),
  ];

  return simnet.callPublicFn(POX_CONTRACT, "stack-stx", stackStxArgs, sender);
};

export const delegateStx = (
  amount: number,
  delegateTo: string,
  untilBurnHeight: number | null,
  poxAddr: string | null,
  sender: string
) => {
  const delegateStxArgs = [
    Cl.uint(amount),
    Cl.principal(delegateTo),
    untilBurnHeight ? Cl.some(Cl.uint(untilBurnHeight)) : Cl.none(),
    poxAddr ? Cl.some(poxAddressToTuple(poxAddr)) : Cl.none(),
  ];

  return simnet.callPublicFn(
    POX_CONTRACT,
    "delegate-stx",
    delegateStxArgs,
    sender
  );
};

export const delegateStackStx = (
  stacker: string,
  amount: number,
  poxAddr: string,
  startBurnHeight: number,
  lockPeriod: number,
  sender: string
) => {
  const delegateStackStxArgs = [
    Cl.principal(stacker),
    Cl.uint(amount),
    poxAddressToTuple(poxAddr),
    Cl.uint(startBurnHeight),
    Cl.uint(lockPeriod),
  ];
  return simnet.callPublicFn(
    POX_CONTRACT,
    "delegate-stack-stx",
    delegateStackStxArgs,
    sender
  );
};

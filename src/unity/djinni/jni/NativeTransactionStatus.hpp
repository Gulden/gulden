// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from libunity.djinni

#pragma once

#include "djinni_support.hpp"
#include "transaction_status.hpp"

namespace djinni_generated {

class NativeTransactionStatus final : ::djinni::JniEnum {
public:
    using CppType = ::TransactionStatus;
    using JniType = jobject;

    using Boxed = NativeTransactionStatus;

    static CppType toCpp(JNIEnv* jniEnv, JniType j) { return static_cast<CppType>(::djinni::JniClass<NativeTransactionStatus>::get().ordinal(jniEnv, j)); }
    static ::djinni::LocalRef<JniType> fromCpp(JNIEnv* jniEnv, CppType c) { return ::djinni::JniClass<NativeTransactionStatus>::get().create(jniEnv, static_cast<jint>(c)); }

private:
    NativeTransactionStatus() : JniEnum("unity_wallet/jniunifiedbackend/TransactionStatus") {}
    friend ::djinni::JniClass<NativeTransactionStatus>;
};

}  // namespace djinni_generated

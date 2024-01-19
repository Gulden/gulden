// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from libunity.djinni

package unity_wallet.jniunifiedbackend;

/**Data record representing a link between an account and an external service (e.g. Holdin.com) */
public final class AccountLinkRecord {


    /*package*/ final String mServiceName;

    /*package*/ final String mServiceData;

    public AccountLinkRecord(
            String serviceName,
            String serviceData) {
        this.mServiceName = serviceName;
        this.mServiceData = serviceData;
    }

    /** What service is it (each service should use a unique string to identify itself)  */
    public String getServiceName() {
        return mServiceName;
    }

    /** Any data unique to the service, e.g. a key used for secure communication or similar */
    public String getServiceData() {
        return mServiceData;
    }

    @Override
    public String toString() {
        return "AccountLinkRecord{" +
                "mServiceName=" + mServiceName +
                "," + "mServiceData=" + mServiceData +
        "}";
    }

}